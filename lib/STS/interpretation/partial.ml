open Common
open Number
open Prelude
open Aux
open Def
module Ident = Vpl.UserInterface.Lift_Ident (String)

module TermQ = struct
  type t = Vpl.WrapperTraductors.Interface(Vpl.Domains.UncertifiedQ.Coeff).Term.t

  let to_term t = t
  let of_term t = t
end

module TermZ = struct
  type t = Vpl.WrapperTraductors.Interface(Vpl.Domains.UncertifiedZ.Coeff).Term.t

  let to_term t = t
  let of_term t = t
end

module DZ = struct
  include Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedZ) (Ident) (TermZ)

  let equal x y = leq x y && leq y x

  let not d =
    if is_bottom d
    then Seq.singleton top
    else (
      let constraints = get_cstrs d in
      constraints
      |> List.to_seq
      (* expand each linear condition into itself and its complement *)
      |> Seq.map (fun c ->
        let open Vpl.Cstr_type in
        let open Vpl.Cstr.Rat in
        match c.typ with
        | Eq ->
          let left, right = split c in
          List.to_seq [ c; left; right ]
        | _ -> Seq.cons (Vpl.Cstr.Rat.compl c) (Seq.singleton c))
        (* make combinations of all variants between original and complemented linear condition *)
      |> Seq.product_seq (* construct domain from linear inequations *)
      |> Seq.map (fun cstr -> assume (of_cond (Cond.of_cstrs (List.of_seq cstr))) top)
        (* filter out original d *)
      |> Seq.filter (not << equal d))
  ;;

  let to_string z =
    if is_bottom z
    then "bottom"
    else (
      let cstrs = get_cstrs z in
      if List.is_empty cstrs
      then "top"
      else List.to_string ~sep:" && " (Vpl.Cstr.Rat.to_string Ident.ofVar) cstrs)
  ;;
end

module DQ = struct
  include Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedQ) (Ident) (TermQ)

  let equal x y = leq x y && leq y x

  let not d =
    if is_bottom d
    then Seq.singleton top
    else (
      let constraints = get_cstrs d in
      constraints
      |> List.to_seq
      (* expand each linear condition into itself and its complement *)
      |> Seq.map (fun c ->
        let open Vpl.Cstr_type in
        let open Vpl.Cstr.Rat in
        match c.typ with
        | Eq ->
          let left, right = split c in
          List.to_seq [ c; left; right ]
        | _ -> Seq.cons (Vpl.Cstr.Rat.compl c) (Seq.singleton c))
      (* make combinations of all variants between original and complemented linear condition *)
      |> Seq.product_seq
      (* construct domain from linear inequations *)
      |> Seq.map (fun cstr -> assume (of_cond (Cond.of_cstrs (List.of_seq cstr))) top)
      (* filter out original d *)
      |> Seq.filter (not << equal d))
  ;;

  let of_rational x =
    let num, den = Rational.to_int2 x in
    Q.make (Z.of_int num) (Z.of_int den)
  ;;

  let to_string q =
    if is_bottom q
    then "bottom"
    else (
      let cstrs = get_cstrs q in
      if List.is_empty cstrs
      then "top"
      else List.to_string ~sep:" && " (Vpl.Cstr.Rat.to_string Ident.ofVar) cstrs)
  ;;
end

let input_to_interface ({ rationals; integers; bools } : inputs) =
  { integer =
      (fun v ->
        Option.map_or ~default:DZ.top (fun c ->
          DZ.assume
            (DZ.of_cond
             @@ DZ.Cond.Atom
                  ( DZ.Term.Var (Ident.toVar v)
                  , Vpl.Cstr_type.EQ
                  , DZ.Term.Cte (DZ.Coeff.of_int c) ))
            DZ.top)
        @@ VarMap.find_opt v integers)
  ; rational =
      (fun v ->
        Option.map_or ~default:DQ.top (fun c ->
          DQ.assume
            (DQ.of_cond
             @@ DQ.Cond.Atom
                  ( DQ.Term.Var (Ident.toVar v)
                  , Vpl.Cstr_type.EQ
                  , DQ.Term.Cte (DQ.of_rational c) ))
            DQ.top)
        @@ VarMap.find_opt v rationals)
  ; bool = (fun v -> VarMap.value ~default:false v bools)
  }
;;

module DQZ = struct
  (** Reduced domain on [Q x Z]. *)
  type t = DQ.t * DZ.t

  let top = DQ.top, DZ.top
  let bottom = DQ.bottom, DZ.bottom
  let is_not_bottom (q, z) = (not (DZ.is_bottom z)) && not (DQ.is_bottom q)

  let not (q, z) =
    let nz = Seq.memoize (DZ.not z)
    and nq = Seq.memoize (DQ.not q) in
    Seq.append_list
      [ Seq.product nq nz; Seq.product nq (Seq.repeat z); Seq.product (Seq.repeat q) nz ]
    |> Seq.filter is_not_bottom
    |> List.of_seq
  ;;

  let meet (q1, z1) (q2, z2) : t = DQ.meet q1 q2, DZ.meet z1 z2
  let to_string (q, z) = Printf.sprintf "Q{%s}Z{%s}" (DQ.to_string q) (DZ.to_string z)
end

module type Conj = sig
  type t

  val top : t
  val bottom : t
  val meet : t -> t -> t
  val is_not_bottom : t -> bool
  val to_string : t -> string
  val not : t -> t list
end

module Disj (Conj : Conj) = struct
  (** Type of disjunctions. Represented as list of conjunctions. *)
  type t = Conj.t list

  let return e : t = [ e ]
  let return2 e1 e2 : t = [ e1; e2 ]
  let bottom : t = [ Conj.bottom ]
  let top : t = return Conj.top

  let normalize conjs =
    let conjs = List.filter Conj.is_not_bottom conjs in
    match conjs with
    | [] -> [ Conj.bottom ]
    | list -> list
  ;;

  let ( && ) s1 s2 : t =
    Seq.product (List.to_seq s1) (List.to_seq s2)
    |> Seq.map (Tuple.fn2 Conj.meet)
    |> List.of_seq
    |> normalize
  ;;

  let ( || ) s1 s2 : t = List.append s1 s2 |> normalize
  let is_bottom l = not @@ List.exists Conj.is_not_bottom l
  let to_string conjunctions = List.to_string ~sep:" || \n" Conj.to_string conjunctions

  let not conjunctions : t =
    let r =
      conjunctions |> List.map (List.to_seq << Conj.not) |> List.to_seq |> Seq.product_seq
    in
    r |> Seq.map (fun s -> Seq.reduce_left Conj.meet Fun.id s) |> List.of_seq |> normalize
  ;;

  let bool_equal x y = (x && y) || ((not x) && not y)
end

(** Module of propositions on [Q x Z]. *)
module DQZF = Disj (DQZ)

(** Module for partial Boolean function evaluation.*)
module Dual = struct
  (** Type representing conditions on numerical variables of when Boolean function returns true and false. *)
  type bool_result = DQZF.t * DQZF.t

  let wrap_const_bool c = if c then DQZF.top, DQZF.bottom else DQZF.bottom, DQZF.top
  let not = Tuple.swap2
  let equal (t1, f1) (t2, f2) = DQZF.((t1 && t2) || (f1 && f2), (t1 && f2) || (f1 && t2))
  let ( && ) (t1, f1) (t2, f2) : bool_result = DQZF.(t1 && t2, f1 || f2)
  let ( || ) (t1, f1) (t2, f2) : bool_result = DQZF.(t1 || t2, f1 && f2)
  let all = List.reduce_left ( && ) Fun.id
  let any = List.reduce_left ( || ) Fun.id

  (** Type of numerical function returns, conditioned with a proposition on variables. *)
  type 'e result = (DQZF.t * 'e) list

  type int_result = DZ.a_expr result
  type rat_result = DQ.a_expr result

  (** Constructs pair of conditions for when the relation is satisfied and not. *)
  let do_rel ~of_relation ~apply (l : 'a result) (r : 'a result) rel : bool_result =
    let open Vpl.Cstr_type in
    List.cartesian l r
    |> List.map (fun ((d1, e1), (d2, e2)) ->
      let both = DQZF.(d1 && d2) in
      let assume_in_formula cond = List.map (apply cond) both in
      let convex_comparisons relt relf =
        let tcond = of_relation (e1, relt, e2)
        and fcond = of_relation (e1, relf, e2) in
        assume_in_formula tcond, assume_in_formula fcond
      in
      let equal_comparisons () =
        let t = of_relation (e1, EQ, e2)
        and f1 = of_relation (e1, LT, e2)
        and f2 = of_relation (e1, GT, e2) in
        let t = assume_in_formula t
        and f = List.append (assume_in_formula f1) (assume_in_formula f2) in
        t, f
      in
      match rel with
      | `Less -> convex_comparisons LT GE
      | `LessEq -> convex_comparisons LE GT
      | `More -> convex_comparisons GT LE
      | `MoreEq -> convex_comparisons GE LT
      | `Eq -> equal_comparisons ()
      | `Neq -> not @@ equal_comparisons ())
    |> List.reduce_left ( || ) Fun.id
  ;;

  let int_do_rel (l : int_result) (r : int_result) rel : bool_result =
    let of_relation (e1, rel, e2) = DZ.of_cond @@ DZ.Cond.Atom (e1, rel, e2)
    and apply cond (q, z) = q, DZ.assume cond z in
    do_rel ~of_relation ~apply l r rel
  ;;

  let rat_do_rel (l : rat_result) (r : rat_result) rel : bool_result =
    let of_relation (e1, rel, e2) = DQ.of_cond @@ DQ.Cond.Atom (e1, rel, e2)
    and apply cond (q, z) = DQ.assume cond q, z in
    do_rel ~of_relation ~apply l r rel
  ;;

  (** When expression is not conditioned with a predicate, such as constant. *)
  let wrap_const_result e = [ DQZF.top, e ]
end

let get_iqueue state var = state.int_queue var
let get_rqueue state var = state.rat_queue var

(** Paritally evaluate Boolean formula given state and input values. Returns conditions of when the function returns true and false. *)
let rec eval_bool
          (state : 'sv state_interface)
          (inputs : ('iv, DZ.t, DQ.t) input_interface)
          (expr : ('sv, 'iv) bool_expr)
  : Dual.bool_result
  =
  let result =
    match expr with
    | BConst c -> Dual.wrap_const_bool c
    | BStateVar v -> Dual.wrap_const_bool (state.bool v)
    | BInputVar v -> Dual.wrap_const_bool (inputs.bool v)
    | BNot e -> Dual.not (eval_bool state inputs e)
    | BAnd conjunctions -> List.map (eval_bool state inputs) conjunctions |> Dual.all
    | BOr disjunctions -> List.map (eval_bool state inputs) disjunctions |> Dual.any
    | BEq (e1, e2) -> Dual.equal (eval_bool state inputs e1) (eval_bool state inputs e2)
    | BNeq (e1, e2) ->
      Dual.not (Dual.equal (eval_bool state inputs e1) (eval_bool state inputs e2))
    | BImply (e1, e2) ->
      Dual.((not (eval_bool state inputs e1)) || eval_bool state inputs e2)
    | IntComp (e1, rel, e2) ->
      let l = eval_integer state inputs e1
      and r = eval_integer state inputs e2 in
      Dual.int_do_rel l r rel
    | RatComp (e1, rel, e2) ->
      Dual.rat_do_rel (eval_rational state inputs e1) (eval_rational state inputs e2) rel
    | BITE { cond; if_true; if_false } ->
      let t, f = eval_bool state inputs cond in
      let tt, tf =
        if DQZF.is_bottom t then DQZF.bottom, DQZF.top else eval_bool state inputs if_true
      and ft, ff =
        if DQZF.is_bottom f
        then DQZF.top, DQZF.bottom
        else eval_bool state inputs if_false
      in
      DQZF.((t && tt) || (f && ft), (t && tf) || (f && ff))
    | IntQueuePositive q ->
      Dual.wrap_const_bool @@ Queue.for_all (Integer.less_eq 0) (get_iqueue state q)
  in
  (* trace expr result; *)
  result

(** Evaluate integer expression given state and input values. *)
and eval_integer state inputs : _ -> Dual.int_result = function
  | IConst c -> Dual.wrap_const_result @@ DZ.Term.Cte (DZ.Coeff.of_int c)
  | IStateVar var ->
    Dual.wrap_const_result @@ DZ.Term.Cte (DZ.Coeff.of_int @@ state.integer var)
  | IInputVar var -> [ [ DQ.top, inputs.integer var ], DZ.Term.Var (Ident.toVar var) ]
  | IBinOp (e1, op, e2) ->
    let r1 = eval_integer state inputs e1
    and r2 = eval_integer state inputs e2 in
    List.cartesian r1 r2
    |> List.map (fun ((d1, e1), (d2, e2)) ->
      ( DQZF.(d1 && d2)
      , match op with
        | `Div -> DZ.Term.Div (e1, e2)
        | `Add -> DZ.Term.Add (e1, e2)
        | `Sub -> DZ.Term.Add (e1, DZ.Term.Opp e2)
        | `Mul -> DZ.Term.Mul (e1, e2) ))
  | IPeekFirstQueue qe ->
    Dual.wrap_const_result
    @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.peek @@ get_iqueue state qe)
  | IPeekLastQueue qe ->
    Dual.wrap_const_result
    @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.last @@ get_iqueue state qe)
  | IntQueueLength qe ->
    Dual.wrap_const_result
    @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.length @@ get_iqueue state qe)
  | RatQueueLength qe ->
    Dual.wrap_const_result
    @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.length @@ get_rqueue state qe)
  | IITE { cond; if_true; if_false } ->
    let t, f = eval_bool state inputs cond
    and rt = eval_integer state inputs if_true
    and rf = eval_integer state inputs if_false in
    List.append
      (List.map (fun (d, e) -> DQZF.(t && d), e) rt)
      (List.map (fun (d, e) -> DQZF.(f && d), e) rf)

(** Evaluate rational expression given state and input values. *)
and eval_rational state inputs : _ -> Dual.rat_result = function
  | RConst c -> Dual.wrap_const_result @@ DQ.Term.Cte (DQ.of_rational c)
  | RStateVar var ->
    Dual.wrap_const_result @@ DQ.Term.Cte (DQ.of_rational @@ state.rational var)
  | RInputVar var -> [ [ inputs.rational var, DZ.top ], DQ.Term.Var (Ident.toVar var) ]
  | RBinOp (e1, op, e2) ->
    let r1 = eval_rational state inputs e1
    and r2 = eval_rational state inputs e2 in
    List.cartesian r1 r2
    |> List.map (fun ((d1, e1), (d2, e2)) ->
      ( DQZF.(d1 && d2)
      , match op with
        | `Div -> DQ.Term.Div (e1, e2)
        | `Add -> DQ.Term.Add (e1, e2)
        | `Sub -> DQ.Term.Add (e1, DQ.Term.Opp e2)
        | `Mul -> DQ.Term.Mul (e1, e2) ))
  | RPeekFirstQueue qe ->
    Dual.wrap_const_result
    @@ DQ.Term.Cte (DQ.of_rational @@ Queue.peek @@ get_rqueue state qe)
  | RPeekLastQueue qe ->
    Dual.wrap_const_result
    @@ DQ.Term.Cte (DQ.of_rational @@ Queue.last @@ get_rqueue state qe)
  | RITE { cond; if_true; if_false } ->
    let t, f = eval_bool state inputs cond
    and rt = eval_rational state inputs if_true
    and rf = eval_rational state inputs if_false in
    List.append
      (List.map (fun (d, e) -> DQZF.(t && d), e) rt)
      (List.map (fun (d, e) -> DQZF.(f && d), e) rf)
;;
