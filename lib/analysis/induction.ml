open Prelude
open Denotational

module Make (C : OrderedType) (N : Denotational.Num) = struct
  let lc_init c = Denotational.Syntax.(Const N.zero < c @ 0)
  let lc_connection c i = Denotational.Syntax.((c @ Stdlib.(i - 1)) < c @ i)

  module SetC = Set.Make (C)

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

  let postcondition clocks formulae =
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
    let clocks =
      SetC.elements
      @@ List.fold_left
           (fold_bexp (fun c _ acc ->
              match c with
              | Some c -> SetC.add c acc
              | None -> acc))
           SetC.empty
           formulae
    in
    let post_compound = postcondition clocks formulae in
    let post = use_more_cond_bexp post_compound in
    let cond = inductive_step formulae in
    let pre = precondition post in
    let init = init_cond post_compound in
    init, pre, cond, post
  ;;
end
