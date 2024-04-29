open Prelude
open Denotational

module type Var = sig
  include OrderedType

  val to_string : t -> string
end

module Make (C : Var) (N : Denotational.Num) = struct
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

  let to_polyhedra man index_name formula =
    let open Apron in
    let formula = norm formula in
    let pp_var v i = Printf.sprintf "%s[%i]" (C.to_string v) i in
    let clock_vars =
      fold_bexp
        (fun v i acc ->
          match v with
          | Some v ->
            let var = pp_var v i in
            Var.of_string var :: acc
          | None -> acc)
        []
        formula
    in
    let index_var = Var.of_string (C.to_string index_name) in
    let env = Apron.Environment.make [| index_var |] (Array.of_list clock_vars) in
    let op2op = function
      | Add -> Texpr1.Add
      | Sub -> Texpr1.Sub
      | Mul -> Texpr1.Mul
      | Div -> Texpr1.Div
    in
    let rec te2te = function
      | TagVar (v, i) -> Texpr1.var env (Var.of_string (pp_var v i))
      | Index i ->
        Texpr1.binop
          Texpr1.Add
          (Texpr1.var env index_var)
          (Texpr1.cst env (Coeff.s_of_int i))
          Texpr1.Int
          Texpr1.Near
      | Const c -> Texpr1.cst env (Coeff.s_of_mpqf c)
      | Op (l, op, r) -> Texpr1.binop (op2op op) (te2te l) (te2te r) Texpr1.Real Near
      | ZeroCond _ ->
        invalid_arg "conditionals should not appear at polyhedra translation"
    in
    let rec fold_formula domain = function
      | And [] -> domain
      | And list -> List.fold_left fold_formula domain list
      | Or _ -> invalid_arg "polyhedra only supports conjunctions"
      | Linear (l, op, r) ->
        let diff = Texpr1.binop Texpr1.Sub (te2te l) (te2te r) Texpr1.Real Texpr1.Near in
        let op, expr =
          match op with
          | Eq -> Tcons1.EQ, diff
          | Less -> Tcons1.SUPEQ, Texpr1.unop Texpr1.Neg diff Texpr1.Real Texpr1.Near
          | LessEq -> Tcons1.SUP, Texpr1.unop Texpr1.Neg diff Texpr1.Real Texpr1.Near
          | More -> Tcons1.SUP, diff
          | MoreEq -> Tcons1.SUPEQ, diff
        in
        let lincond = Tcons1.make expr op in
        (* let _ = Format.printf "%a" Tcons1.print lincond in *)
        let array = Tcons1.array_make env 1 in
        let _ = Tcons1.array_set array 0 lincond in
        Abstract1.meet_tcons_array man domain array
    in
    fold_formula (Abstract1.top man env) formula
  ;;
end

let%test_module _ =
  (module struct
    module A = struct
include Make (String) (Number.Rational)
      include MakeDebug(String)(Number.Rational)

end
    

    let man = Polka.manager_alloc_loose ()

    let%test_unit _ =
      assert (Apron.Abstract1.is_top man (A.to_polyhedra man "i" (And [])))
    ;;
    let%test_unit _ =
      let c = Rtccsl.Precedence {cause="a"; effect="b"} in
      let formula = Denotational.exact_rel c in
      (* let _ = Printf.printf "%s\n" (A.string_of_bool_expr formula) in *)
      assert (not @@ Apron.Abstract1.is_bottom man (A.to_polyhedra man "i" formula))
    ;;
  end)
;;
