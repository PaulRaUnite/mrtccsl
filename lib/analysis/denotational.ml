open Prelude
open Sexplib0.Sexp_conv

(*TODO: refactor numerical and boolean formula into their own modules?*)

type num_op =
  | Add
  | Sub
  | Mul
  | Div
[@@deriving sexp]

type ('c, 'n) tag_expr =
  | TagVar of 'c * int
  | Const of 'n
  | Index of int
  | Op of ('c, 'n) tag_expr * num_op * ('c, 'n) tag_expr
  | ZeroCond of ('c, 'n) tag_expr * 'n
    (*needed because otherwise will collide with max in factoring out min/max*)
  | Min of ('c, 'n) tag_expr * ('c, 'n) tag_expr
  | Max of ('c, 'n) tag_expr * ('c, 'n) tag_expr
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
  | Linear of ('c, 'n) tag_expr * num_rel * ('c, 'n) tag_expr
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

let rec fold_texp f acc = function
  | TagVar (v, i) -> f (Some v) i acc
  | Op (left, _, right) | Min (left, right) | Max (left, right) ->
    let acc = fold_texp f acc left in
    fold_texp f acc right
  | Index i -> f None i acc
  | Const _ -> acc
  | ZeroCond (more, _) -> fold_texp f acc more
;;

let rec fold_bexp f acc = function
  | Or list | And list -> List.fold_left (fold_bexp f) acc list
  | Linear (left, _, right) ->
    let acc = fold_texp f acc left in
    fold_texp f acc right
;;

let rec map_ind_texp f = function
  | TagVar (v, i) -> TagVar (v, f (Some v) i)
  | Index i -> Index (f None i)
  | Const c -> Const c
  | Op (left, op, right) -> Op (map_ind_texp f left, op, map_ind_texp f right)
  | ZeroCond (more, init_value) -> ZeroCond (map_ind_texp f more, init_value)
  | Min (l, r) -> Min (map_ind_texp f l, map_ind_texp f r)
  | Max (l, r) -> Max (map_ind_texp f l, map_ind_texp f r)
;;

let rec map_ind_bexp f = function
  | Or list -> Or (List.map (map_ind_bexp f) list)
  | And list -> And (List.map (map_ind_bexp f) list)
  | Linear (left, op, right) -> Linear (map_ind_texp f left, op, map_ind_texp f right)
;;

let rec use_more_cond_texp = function
  | ZeroCond (more, _) -> more
  | Op (l, op, r) -> Op (use_more_cond_texp l, op, use_more_cond_texp r)
  | _ as e -> e
;;

let rec use_more_cond_bexp = function
  | Or list -> Or (List.map use_more_cond_bexp list)
  | And list -> And (List.map use_more_cond_bexp list)
  | Linear (l, op, r) -> Linear (use_more_cond_texp l, op, use_more_cond_texp r)
;;

let rec fact_disj_texp exp =
  match exp with
  | TagVar _ | Index _ | Const _ | ZeroCond _ -> [ [], exp ]
  | Op (l, op, r) ->
    let lvariants = fact_disj_texp l in
    let rvariants = fact_disj_texp r in
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

(** Factors out disjunctions from semi-linear formula into a list of linear ones. *)
let rec fact_disj_bexp = function
  | Or list -> List.flat_map fact_disj_bexp list
  | And list ->
    List.map (fun l -> And l) (List.general_cartesian (List.map fact_disj_bexp list))
  | Linear (l, op, r) ->
    let lvariants = fact_disj_texp l in
    let rvariants = fact_disj_texp r in
    List.cartesian lvariants rvariants
    |> List.map (fun ((lcond, l), (rcond, r)) ->
      And ((Linear (l, op, r) :: lcond) @ rcond))
;;

let empty_bexp = function
  | Or [] | And [] -> true
  | _ -> false
;;

let rec texp_reduce f e =
  let reduce = texp_reduce f in
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
  f r
;;

let rec bexp_reduce f g e =
  let reduce = bexp_reduce f g in
  let r =
    match e with
    | And list -> And (List.map reduce list)
    | Or list -> Or (List.map reduce list)
    | Linear (l, op, r) -> Linear (f l, op, f r)
  in
  g r
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
  | _ as lin -> lin
;;

let norm e = bexp_reduce Fun.id norm_rule e

open Prelude

module MakeDebug (V : Interface.Debug) (N : Interface.Debug) = struct
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
end
