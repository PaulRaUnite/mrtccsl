open Prelude

module type Var = sig
  open Interface
  include OrderedType
  include Stringable with type t := t
end

module type Num = sig
  type t

  val zero : t
end

module Preprocess (C : Var) (N : Num) = struct
  open Denotational

  let lc_init c = Denotational.Syntax.(Const N.zero < c @ 0)
  let lc_connection c i = Denotational.Syntax.((c @ Stdlib.(i - 1)) < c @ i)

  module SetCI = Set.Make (struct
      type t = C.t * int

      let compare (c1, i1) (c2, i2) =
        let comp = C.compare c1 c2 in
        if comp = 0 then Int.compare i1 i2 else comp
      ;;
    end)

  let collect_vars formula =
    let vars =
      fold_bexp
        (fun x i set ->
          match x with
          | Some v -> SetCI.add (v, i) set
          | None -> set)
        SetCI.empty
        formula
    in
    vars
  ;;

  let inductive_step formula =
    let vars =
      SetCI.elements
      @@ List.fold_left
           (fun acc f -> SetCI.union acc (collect_vars f))
           SetCI.empty
           formula
    in
    use_more_cond_bexp @@ And (formula @ List.map (fun (c, i) -> lc_connection c i) vars)
  ;;

  let clocks_of formulae =
    let module SetC = Set.Make (C) in
    let fold_formula =
      fold_bexp (fun c _ acc ->
        match c with
        | Some c -> SetC.add c acc
        | None -> acc)
    in
    let clocks_set = List.fold_left fold_formula SetC.empty formulae in
    SetC.elements clocks_set
  ;;

  let postcondition formulae =
    let clocks = clocks_of formulae in
    let intervals =
      List.map (fold_bexp (fun _ i (l, r) -> Int.(min i l, max i r)) (0, 0)) formulae
    in
    let min, max =
      List.fold_left
        (fun (gmin, gmax) (lmin, lmax) -> Int.(min gmin lmin, max gmax lmax))
        (0, 0)
        intervals
    in
    let neg_ints = List.init (Int.neg min + 1) Int.neg in
    let clock_connections =
      List.map (fun (c, i) -> lc_connection c i) (List.cartesian clocks neg_ints)
    in
    let _ = assert (max = 0) in
    let expand f min =
      let neg_ints = List.init (Int.neg min + 1) Int.neg in
      List.map (fun i -> map_ind_bexp (fun _ j -> i + j) f) neg_ints
    in
    let expanded_formulae =
      List.flatten
      @@ List.map (fun (f, (lmin, _)) -> expand f (min - lmin))
      @@ List.combine formulae intervals
    in
    And (expanded_formulae @ clock_connections)
  ;;

  let precondition post = map_ind_bexp (fun _ i -> i - 1) post

  let init_cond post =
    let rec init_cond_texp = function
      | ZeroCond (_, init) -> Const init
      | Op (l, op, r) -> Op (init_cond_texp l, op, init_cond_texp r)
      | TagVar (_, i) when i = 0 -> Const N.zero
      | _ as e -> e
    in
    let rec init_cond_bexp = function
      | Or list -> Or (List.map init_cond_bexp list)
      | And list -> And (List.map init_cond_bexp list)
      | Linear (l, op, r) -> Linear (init_cond_texp l, op, init_cond_texp r)
    in
    let min, max = fold_bexp (fun _ i (l, r) -> Int.(min i l, max i r)) (0, 0) post in
    let _ = assert (max = 0) in
    let post = map_ind_bexp (fun _ i -> i - min) post in
    let post = init_cond_bexp post in
    post
  ;;

  let proof_obligations formulae =
    let post_compound = postcondition formulae in
    let post = use_more_cond_bexp post_compound in
    let cond = inductive_step formulae in
    let pre = precondition post in
    let init = init_cond post_compound in
    init, pre, cond, post
  ;;
end

module type Domain = sig
  type t
  type v
  type n

  val top : v -> (v * int) list -> t
  val add_constraint : v -> t -> (v, n) Denotational.bool_expr -> t
  val leq : t -> t -> bool
  val is_bottom : t -> bool
  val is_top : t -> bool

  include Interface.Stringable with type t := t
end

module type Alloc = sig
  type dom

  val alloc : dom Apron.Manager.t
end

exception NonConvex

module PolkaDomain
    (A : Alloc)
    (V : Var)
    (N : sig
       type t

       val to_rational : t -> Number.Rational.t
     end) =
struct
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
      | TagVar (v, i) ->
        let var = Var.of_string (pp_var (v, i)) in
        Texpr1.var env var
      | Index i ->
        Texpr1.binop
          Texpr1.Add
          (Texpr1.var env index_var)
          (Texpr1.cst env (Coeff.s_of_int i))
          Texpr1.Int
          Texpr1.Near
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
end

module VPLDomain
    (V : Var)
    (N : sig
       type t

       val to_rational : t -> Number.Rational.t
     end) =
struct
  open Denotational
  module Ident = Vpl.UserInterface.Lift_Ident (String)

  module Term = struct
    type t = Vpl.WrapperTraductors.Interface(Vpl.Domains.UncertifiedQ.Coeff).Term.t

    let to_term t = t
    let of_term t = t
  end

  module D = Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedQ) (Ident) (Term)

  type t = Vpl.UserInterface.UncertifiedQ.t
  type v = V.t
  type n = N.t

  let to_q x =
    let x = N.to_rational x in
    let num = Mpz.get_int (Mpqf.get_num x) in
    let den = Mpz.get_int (Mpqf.get_den x) in
    Q.make (Z.of_int num) (Z.of_int den)
  ;;

  let var (v, i) = Ident.toVar @@ Printf.sprintf "%s[%i]" (V.to_string v) i
  let top _ _ = D.top
  let leq = D.leq
  let is_top d = d = D.top
  let is_bottom = D.is_bottom
  let to_string = D.to_string V.to_string

  let rec te2ae index = function
    | TagVar (v, i) -> D.Term.Var (var (v, i))
    | Const n -> D.Term.Cte (to_q n)
    | Index i ->
      D.Term.Add (D.Term.Var (Ident.toVar @@ V.to_string index), D.Term.Cte (Q.of_int i))
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
    | Eq -> Vpl.Cstr_type.EQ
    | More -> Vpl.Cstr_type.GT
    | Less -> Vpl.Cstr_type.LT
    | MoreEq -> Vpl.Cstr_type.GE
    | LessEq -> Vpl.Cstr_type.LE
  ;;

  let rec add_constraint index domain = function
    | And [] -> domain
    | And list -> List.fold_left (add_constraint index) domain list
    | Or _ -> invalid_arg "polyhedra only supports conjunctions"
    | Linear (l, op, r) ->
      let lincond = D.Cond.Atom (te2ae index l, op2op op, te2ae index r) in
      D.assume (D.of_cond lincond) domain
  ;;
end

module Analysis (D : Domain) = struct
  let to_polyhedra index_name formula =
    let formula = Denotational.norm formula in
    let clock_vars =
      Denotational.fold_bexp
        (fun v i acc ->
          match v with
          | Some v -> (v, i) :: acc
          | None -> acc)
        []
        formula
    in
    D.add_constraint index_name (D.top index_name clock_vars) formula
  ;;

  type report = unit

  (* let analyze index_name spec assertion : report = () *)
end

module Test
    (MakeDomain : functor
       (V : Var)
       (N : sig
          type t

          val to_rational : t -> Number.Rational.t
        end)
       -> Domain with type v = V.t and type n = N.t) =
struct
  module N = struct
    include Number.Rational

    let to_rational = Fun.id
  end

  module A = struct
    include Preprocess (String) (N)
    include Denotational.MakeDebug (String) (N)
  end

  module D = MakeDomain (String) (N)
  module An = Analysis (D)

  let%test_unit _ = assert (D.is_top (An.to_polyhedra "i" (And [])))
  let%test_unit _ = assert (not @@ D.is_bottom (An.to_polyhedra "i" (And [])))

  let%test_unit _ =
    let c = Rtccsl.Precedence { cause = "a"; effect = "b" } in
    let formula = Denotational.Rtccsl.exact_rel c in
    let domain = An.to_polyhedra "i" formula in
    let _ = Printf.printf "%s\n" (A.string_of_bool_expr formula) in
    let _ = Format.printf "%s" (D.to_string domain) in
    assert (not @@ D.is_bottom domain)
  ;;
end

let%test_module _ =
  (module struct
    include Test (PolkaDomain (struct
        type dom = Polka.loose Polka.t

        let alloc = Polka.manager_alloc_loose ()
      end))
  end)
;;

let%test_module _ =
  (module struct
    include Test (VPLDomain)
  end)
;;
