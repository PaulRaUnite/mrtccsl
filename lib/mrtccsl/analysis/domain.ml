open Prelude
open Expr

module type Var = sig
  open Interface
  include OrderedType
  include Interface.Debug with type t := t
end

module type Num = sig
  include Interface.Debug

  val to_rational : t -> Number.Rational.t
end

module type S = sig
  type t
  type v
  type n

  val top : v -> (v * int) list -> t
  val add_constraint : v -> t -> (v, n) Denotational.bool_expr -> t
  val leq : t -> t -> bool
  val is_bottom : t -> bool
  val is_top : t -> bool
  val meet : t -> t -> t
  val diff : t -> t -> t list
  val more_precise : t -> t -> bool
  val infinite_in : v -> t -> bool
  val set_debug : bool -> unit
  val project : v list -> t -> t

  include Interface.Stringable with type t := t
end

module type Alloc = sig
  type dom

  val alloc : dom Apron.Manager.t
end

exception NonConvex

module Polka (A : Alloc) (V : Var) (N : Num) = struct
  open Denotational
  open Apron

  type t = A.dom Abstract1.t
  type n = N.t
  type v = V.t

  let pp_var (v, i) = Printf.sprintf "%s[%i]" (V.to_string v) i
  let v_to_var = Var.of_string << V.to_string

  let top index reals =
    let index_var = v_to_var index in
    let reals = Array.of_seq (Seq.map (Var.of_string << pp_var) (List.to_seq reals)) in
    Abstract1.top A.alloc (Environment.make [| index_var |] reals)
  ;;

  let rec add_constraint index domain =
    let env = Abstract1.env domain in
    let index_var = v_to_var index in
    let op2op = function
      | Add -> Texpr1.Add
      | Sub -> Texpr1.Sub
      | Mul -> Texpr1.Mul
      | Div -> Texpr1.Div
    in
    let rec te2te = function
      | Var v ->
        (match v with
         | FreeVar v -> Texpr1.var env (Var.of_string (V.to_string v))
         | ClockVar (v, i) ->
           let var = Var.of_string (pp_var (v, i)) in
           Texpr1.var env var
         | Index i ->
           Texpr1.binop
             Texpr1.Add
             (Texpr1.var env index_var)
             (Texpr1.cst env (Coeff.s_of_int i))
             Texpr1.Int
             Texpr1.Near)
      | Const c -> Texpr1.cst env (Coeff.s_of_mpqf @@ N.to_rational c)
      | Op (l, op, r) -> Texpr1.binop (op2op op) (te2te l) (te2te r) Texpr1.Real Near
      | ZeroCond _ | Min _ | Max _ -> raise NonConvex
    in
    function
    | And [] -> domain
    | And list -> List.fold_left (add_constraint index) domain list
    | Or _ -> invalid_arg "polyhedra only supports conjunctions"
    | Linear (l, op, r) ->
      let diff = Texpr1.binop Texpr1.Sub (te2te l) (te2te r) Texpr1.Real Texpr1.Near in
      let op, expr =
        match op with
        | Neq -> failwith "neq is not convex"
        | Eq -> Tcons1.EQ, diff
        | Less -> Tcons1.SUP, Texpr1.unop Texpr1.Neg diff Texpr1.Real Texpr1.Near
        | LessEq -> Tcons1.SUPEQ, Texpr1.unop Texpr1.Neg diff Texpr1.Real Texpr1.Near
        | More -> Tcons1.SUP, diff
        | MoreEq -> Tcons1.SUPEQ, diff
      in
      let lincond = Tcons1.make expr op in
      let _ = Format.printf "%a\n" Tcons1.print lincond in
      let array = Tcons1.array_make env 1 in
      let _ = Tcons1.array_set array 0 lincond in
      Abstract1.meet_tcons_array A.alloc domain array
  ;;

  let leq = Apron.Abstract1.is_leq A.alloc
  let is_bottom = Apron.Abstract1.is_bottom A.alloc
  let is_top = Apron.Abstract1.is_top A.alloc
  let to_string d = Format.asprintf "%a" Abstract1.print d
  let meet = Apron.Abstract1.meet A.alloc
  let diff _ _ = failwith "not implemented"
  let more_precise _ _ = failwith "not implemented"
  let infinite_in _ _ = failwith "not implemented"
  let set_debug _ = ()
  let project _ _ = failwith "not implemented"
end

module VPL (V : Var) (N : Num) = struct
  open Denotational
  open MakeDebug (V) (N)
  module Ident = Vpl.UserInterface.Lift_Ident (String)

  module Term = struct
    type t = Vpl.WrapperTraductors.Interface(Vpl.Domains.UncertifiedQ.Coeff).Term.t

    let to_term t = t
    let of_term t = t
  end

  module D = Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedQ) (Ident) (Term)
  module VarSet = Set.Make (String)

  type aux =
    { b_expr : D.b_expr list
    ; expr : (V.t, N.t) bool_expr list
    ; vars : VarSet.t
    }

  let aux_union x y =
    { b_expr = x.b_expr @ y.b_expr
    ; vars = VarSet.union x.vars y.vars
    ; expr = x.expr @ y.expr
    }
  ;;

  let aux_empty = { b_expr = []; vars = VarSet.empty; expr = [] }

  type t = aux * D.t
  type v = V.t
  type n = N.t

  let is_debug = ref false

  let to_q x =
    let x = N.to_rational x in
    let num = Mpz.get_int (Mpqf.get_num x) in
    let den = Mpz.get_int (Mpqf.get_den x) in
    Q.make (Z.of_int num) (Z.of_int den)
  ;;

  let clock_var_str (v, i) = Printf.sprintf "%s[%i]" (V.to_string v) i
  let clock_var (v, i) = Ident.toVar (clock_var_str (v, i))
  let index_var index = Ident.toVar @@ V.to_string index
  let free_var v = V.to_string v

  let var index = function
    | FreeVar v -> free_var v
    | ClockVar (c, i) -> clock_var_str (c, i)
    | Index _ -> V.to_string index
  ;;

  let top _ _ = aux_empty, D.top
  let leq (_, x) (_, y) = D.leq x y
  let meet (auxx, x) (auxy, y) = aux_union auxx auxy, D.meet x y

  (*FIXME: need more tests to check if it actually works in all cases*)
  let is_top (_, d) = d = D.top
  let is_bottom (_, x) = D.is_bottom x
  let to_string (_, x) = D.to_string V.to_string x

  let rec te2ae index = function
    | Var v ->
      (match v with
       | FreeVar v -> D.Term.Var (Ident.toVar (V.to_string v))
       | ClockVar (v, i) -> D.Term.Var (clock_var (v, i))
       | Index i -> D.Term.Add (D.Term.Var (index_var index), D.Term.Cte (Q.of_int i)))
    | Const n -> D.Term.Cte (to_q n)
    | Op (l, op, r) ->
      let l = te2ae index l in
      let r = te2ae index r in
      (match op with
       | Add -> D.Term.Add (l, r)
       | Sub -> D.Term.Add (l, D.Term.Opp r)
       | Mul -> D.Term.Mul (l, r)
       | Div -> D.Term.Div (l, r))
    | ZeroCond _ | Min _ | Max _ -> raise NonConvex
  ;;

  let op2op = function
    | Neq -> failwith "neq is not convex"
    | Eq -> Vpl.Cstr_type.EQ
    | More -> Vpl.Cstr_type.GT
    | Less -> Vpl.Cstr_type.LT
    | MoreEq -> Vpl.Cstr_type.GE
    | LessEq -> Vpl.Cstr_type.LE
  ;;

  let rec add_constraint index (aux, domain) formula =
    match formula with
    | And [] -> aux, domain
    | And list -> List.fold_left (add_constraint index) (aux, domain) list
    | Or _ -> invalid_arg "polyhedra only supports conjunctions"
    | Linear (l, op, r) ->
      let lincond = D.Cond.Atom (te2ae index l, op2op op, te2ae index r) in
      let bexp = D.of_cond lincond in
      let vars = formula |> BoolExpr.vars |> List.map (var index) |> VarSet.of_list in
      let new_domain = D.assume bexp domain in
      let _ =
        if (not (D.is_bottom domain)) && D.is_bottom new_domain
        then (
          Printf.printf "makes bottom: %s \n\n" (string_of_bool_expr formula);
          print_bool_exprs aux.expr)
      in
      aux_union aux { b_expr = [ bexp ]; vars; expr = [ formula ] }, new_domain
  ;;

  let diff (_, x) (_, y) = List.map (fun x -> aux_empty, x) (D.diff x y)

  (** Checks that b is strictly more precise than a.*)
  let more_precise (aa, a) (ab, b) =
    (* let _ = List.iter (fun v -> Printf.printf "%s " v) (VarSet.elements aa.vars) in *)
    let diffvars = VarSet.diff ab.vars aa.vars |> VarSet.elements in
    let p = D.project diffvars b in
    let _ =
      if !is_debug then
      Printf.printf
        "To diff:\nPre: %s\n Proj: %s\n"
        (D.to_string V.to_string a)
        (D.to_string V.to_string p)
    in
    D.leq a p && D.leq p a
  ;;

  let infinite_in var (_, dom) =
    let var = D.Term.Var (Ident.toVar @@ V.to_string var) in
    D.get_upper_bound var dom
    |> Option.map (function
      | Vpl.Pol.Infty -> true
      | _ -> false)
    |> Option.value ~default:false
  ;;

  let project vars (aux, dom) =
    let vars = List.map V.to_string vars in
    let vars_to_project = VarSet.diff aux.vars (VarSet.of_list vars) in
    let projected = D.project (VarSet.elements vars_to_project) dom in
    (*FIXME: aux is not correct here*)
    aux, projected
  ;;

  let set_debug cond = is_debug := cond
end
