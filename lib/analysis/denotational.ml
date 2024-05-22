open Prelude
open Sexplib0.Sexp_conv

(*Cannot refactor further, because the implementations and definitions depend on each other which requires mutually recursive modules which are simply annoying.*)

type num_op =
  | Add
  | Sub
  | Mul
  | Div
[@@deriving sexp]

type ('c, 'n) num_expr =
  | TagVar of 'c * int
  | Const of 'n
  | Index of int
  | Op of ('c, 'n) num_expr * num_op * ('c, 'n) num_expr
  | ZeroCond of ('c, 'n) num_expr * 'n
  (** [ZeroCond] variant is needed because otherwise will collide with max in factoring out min/max*)
  | Min of ('c, 'n) num_expr * ('c, 'n) num_expr
  | Max of ('c, 'n) num_expr * ('c, 'n) num_expr
[@@deriving sexp]

type num_rel =
  | Eq
  | More
  | Less
  | MoreEq
  | LessEq
[@@deriving sexp]

type ('c, 'n) bool_expr =
  | Or of ('c, 'n) bool_expr list
  | And of ('c, 'n) bool_expr list
  | Linear of ('c, 'n) num_expr * num_rel * ('c, 'n) num_expr
[@@deriving sexp]

module Syntax = struct
  let ( @ ) c i = TagVar (c, i)
  let ( < ) x y = Linear (x, Less, y)
  let ( <= ) x y = Linear (x, LessEq, y)
  let ( > ) x y = Linear (x, More, y)
  let ( >= ) x y = Linear (x, MoreEq, y)
  let ( = ) x y = Linear (x, Eq, y)
  let ( + ) x y = Op (x, Add, y)
  let ( - ) x y = Op (x, Sub, y)
  let ( * ) x y = Op (x, Mul, y)
  let ( / ) x y = Op (x, Div, y)
  let ( |> ) expr (l, r) = And [ l <= expr; expr <= r ]
  let min x y = Min (x, y)
  let max x y = Max (x, y)
  let ( && ) l r = And [ l; r ]
  let ( || ) l r = Or [ l; r ]
end

module NumExpr = struct
  type ('c, 'n) t = ('c, 'n) num_expr

  let rec fold f acc = function
    | TagVar (v, i) -> f (Some v) i acc
    | Op (left, _, right) | Min (left, right) | Max (left, right) ->
      let acc = fold f acc left in
      fold f acc right
    | Index i -> f None i acc
    | Const _ -> acc
    | ZeroCond (more, _) -> fold f acc more
  ;;

  let rec eliminate f e =
    let elim = eliminate f in
    let* e =
      match e with
      | TagVar _ | Const _ | Index _ -> Some e
      | Op (l, op, r) ->
        let* l = elim l in
        let* r = elim r in
        Some (Op (l, op, r))
      | ZeroCond (more, init) ->
        let* more = elim more in
        Some (ZeroCond (more, init))
      | Min (l, r) ->
        let* l = elim l in
        let* r = elim r in
        Some (Min (l, r))
      | Max (l, r) ->
        let* l = elim l in
        let* r = elim r in
        Some (Max (l, r))
    in
    f e
  ;;

  let rec rewrite rule e =
    let reduce = rewrite rule in
    let r =
      match e with
      | TagVar _ | Const _ | Index _ -> e
      | Op (l, op, r) ->
        let l = reduce l in
        let r = reduce r in
        Op (l, op, r)
      | ZeroCond (more, init) -> ZeroCond (reduce more, init)
      | Min (l, r) ->
        let l = reduce l in
        let r = reduce r in
        Min (l, r)
      | Max (l, r) ->
        let l = reduce l in
        let r = reduce r in
        Max (l, r)
    in
    rule r
  ;;

  let rec fact_disj exp =
    match exp with
    | TagVar _ | Index _ | Const _ | ZeroCond _ -> [ [], exp ]
    | Op (l, op, r) ->
      let lvariants = fact_disj l in
      let rvariants = fact_disj r in
      List.cartesian lvariants rvariants
      |> List.map (fun ((lcond, l), (rcond, r)) -> lcond @ rcond, Op (l, op, r))
    | Min (l, r) | Max (l, r) ->
      let lcond = Syntax.(l >= r) in
      let rcond = Syntax.(l <= r) in
      (match exp with
       | Min _ -> [ [ lcond ], r; [ rcond ], l ]
       | Max _ -> [ [ lcond ], l; [ rcond ], r ]
       | _ -> failwith "unreachable")
  ;;

  (** The rule to unpack zerocond expressions.
      i > index -> use indexed expression
      i = index -> use initial condition
      i < index -> remove*)
  let reduce_zerocond_rule index = function
    | ZeroCond (Index i, _) when i > index -> Some (Index i)
    | ZeroCond (Index i, init) when i = index -> Some (Const init)
    | ZeroCond ((TagVar (_, i) as v), _) when i > index -> Some v
    | ZeroCond (TagVar (_, i), init) when i = index -> Some (Const init)
    | ZeroCond _ -> None
    | _ as e -> Some e
  ;;

  (** The rule to remove all expressions that reference non-existent past in initial condition: i < index.*)
  let reduce_negative_rule index = function
    | (Index i | TagVar (_, i)) when i <= index -> None
    | _ as e -> Some e
  ;;
end

module type Num = sig
  include Interface.OrderedType
  include Interface.Number.Field with type t := t
end

module MakeExtNumExpr (N : Num) = struct
  module N = struct
    include N
    include Interface.ExpOrder.Make (N)
  end

  include NumExpr

  let norm_rule expr =
    match expr with
    | Op (Const n, op, Const n') ->
      Const
        (match op with
         | Add -> N.(n + n')
         | Sub -> N.(n - n')
         | Mul -> N.(n * n')
         | Div -> N.(n / n'))
    | Op (Const n, Add, e) | Op (e, Add, Const n) -> if N.equal n N.zero then e else expr
    | Min (Const l, Const r) -> Const (N.min l r)
    | Max (Const l, Const r) -> Const (N.max l r)
    | ZeroCond (Const n, init) -> Const (N.max n init)
    | _ -> expr
  ;;

  let norm f = rewrite norm_rule f
end

module BoolExpr = struct
  type ('c, 'n) t = ('c, 'n) bool_expr

  let rec fold f acc = function
    | Or list | And list -> List.fold_left (fold f) acc list
    | Linear (left, _, right) ->
      let acc = NumExpr.fold f acc left in
      NumExpr.fold f acc right
  ;;

  let rec eliminate f g e =
    let elim = eliminate f g in
    let* e =
      match e with
      | And list ->
        let list = List.filter_map elim list in
        if List.is_empty list then None else Some (And list)
      | Or list ->
        let list = List.filter_map elim list in
        if List.is_empty list then None else Some (Or list)
      | Linear (l, op, r) ->
        let* l = f l
        and* r = f r in
        Some (Linear (l, op, r))
    in
    g e
  ;;

  let rec rewrite f bexp_rule e =
    let reduce = rewrite f bexp_rule in
    let r =
      match e with
      | And list -> And (List.map reduce list)
      | Or list -> Or (List.map reduce list)
      | Linear (l, op, r) -> Linear (f l, op, f r)
    in
    bexp_rule r
  ;;

  let map_idx f e =
    let rule = function
      | TagVar (v, i) -> TagVar (v, f (Some v) i)
      | Index i -> Index (f None i)
      | e -> e
    in
    rewrite (NumExpr.rewrite rule) Fun.id e
  ;;

  let eliminate_zerocond index f =
    eliminate (NumExpr.reduce_zerocond_rule index) Option.some f
  ;;

  let use_more_cond e =
    let use_more_rule = function
      | ZeroCond (more, _) -> more
      | _ as e -> e
    in
    rewrite (NumExpr.rewrite use_more_rule) Fun.id e
  ;;

  let norm_rule = function
    | Or [] -> And []
    | Or [ x ] -> x
    | Or list ->
      let to_flatten, others =
        List.partition_map
          (fun f ->
            match f with
            | Or l -> Either.Left l
            | _ as other -> Either.Right other)
          list
      in
      Or (others @ List.flatten to_flatten)
    | And [ x ] -> x
    | And list ->
      let to_flatten, others =
        List.partition_map
          (fun f ->
            match f with
            | And l -> Either.Left l
            | _ as other -> Either.Right other)
          list
      in
      And (others @ List.flatten to_flatten)
    | Linear (l, More, r) -> Linear (r, Less, l)
    | Linear (l, MoreEq, r) -> Linear (r, LessEq, l)
    | Linear _ as e -> e
  ;;

  let logical_norm e = rewrite Fun.id norm_rule e

  let is_empty = function
    | Or [] | And [] -> true
    | _ -> false
  ;;

  (** Factors out disjunctions from semi-linear formula into a list of linear ones. *)
  let rec fact_disj = function
    | Or list -> List.flat_map fact_disj list
    | And list ->
      List.map (fun l -> And l) (List.general_cartesian (List.map fact_disj list))
    | Linear (l, op, r) ->
      let lvariants = NumExpr.fact_disj l in
      let rvariants = NumExpr.fact_disj r in
      List.cartesian lvariants rvariants
      |> List.map (fun ((lcond, l), (rcond, r)) ->
        And ((Linear (l, op, r) :: lcond) @ rcond))
  ;;

  let vars f = fold (fun c _ acc -> c :: acc) [] f
  let indexed_vars f = fold (fun c i acc -> (c, i) :: acc) [] f

  let vars_except_i f =
    List.filter_map
      (fun (c, i) ->
        let* c = c in
        Some (c, i))
      (indexed_vars f)
  ;;

  let unique_vars comp formula =
    List.sort_uniq (Tuple.compare2 comp Int.compare) (vars_except_i formula)
  ;;

  let shift_by f i = map_idx (fun _ j -> i + j) f
  let is_stateful f = fold (fun _ i acc -> if i <> 0 then true else acc) false f
end

module MakeExpr (N : Num) = struct
  module NumExpr = MakeExtNumExpr (N)

  module BoolExpr = struct
    include BoolExpr

    (** Normalizes boolear expressions to be as small as we can, including numerical part.*)
    let norm f = rewrite NumExpr.norm_rule norm_rule f
  end
end

module MakeDebug (V : Interface.Debug) (N : Interface.Debug) = struct
  open Prelude

  let string_of_num_op = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
  ;;

  let rec string_of_tag_expr = function
    | TagVar (var, ind) ->
      let ind_str =
        match ind with
        | x when x > 0 -> Printf.sprintf "i+%i" x
        | 0 -> "i"
        | x -> Printf.sprintf "i%i" x
      in
      Printf.sprintf "%s[%s]" (V.to_string var) ind_str
    | Const n -> N.to_string n
    | Index i ->
      (match i with
       | x when x > 0 -> Printf.sprintf "i+%i" x
       | 0 -> "i"
       | x -> Printf.sprintf "i%i" x)
    | Op (l, op, r) ->
      Printf.sprintf
        "(%s %s %s)"
        (string_of_tag_expr l)
        (string_of_num_op op)
        (string_of_tag_expr r)
    | ZeroCond (more, init) ->
      Printf.sprintf "(%s when i>0 else %s)" (string_of_tag_expr more) (N.to_string init)
    | Min (l, r) ->
      Printf.sprintf "min(%s, %s)" (string_of_tag_expr l) (string_of_tag_expr r)
    | Max (l, r) ->
      Printf.sprintf "max(%s, %s)" (string_of_tag_expr l) (string_of_tag_expr r)
  ;;

  let string_of_num_rel = function
    | Eq -> "="
    | More -> ">"
    | Less -> "<"
    | MoreEq -> ">="
    | LessEq -> "<="
  ;;

  let string_of_bool_expr =
    let rec aux level =
      let padding = String.make (2 * level) ' ' in
      let concat delim l =
        let s =
          List.fold_left
            (fun acc el ->
              Printf.sprintf "%s\n%s%s %s" acc padding delim (aux (level + 1) el))
            ""
            l
        in
        if List.is_one l || level = 0 then s else Printf.sprintf "(%s\n)" s
      in
      function
      | Or list -> concat "V" list
      | And list -> concat "⋀" list
      | Linear (l, op, r) ->
        Printf.sprintf
          "%s %s %s"
          (string_of_tag_expr l)
          (string_of_num_rel op)
          (string_of_tag_expr r)
    in
    aux 0
  ;;

  let print_bool_exprs list =
    List.iter (fun f -> Printf.printf "%s\n" (string_of_bool_expr f)) list
  ;;
end
