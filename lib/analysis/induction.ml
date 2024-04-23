open Prelude
open Denotational

module Make (C : OrderedType) (N : Denotational.Num) = struct
  let lc_init c = Denotational.Syntax.(Const N.zero < c @ 0)
  let lc_connection c = Denotational.Syntax.(c @ -1 < c @ 0)

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
    And (formula @ List.map (fun (c, i) -> Syntax.((c @ Int.(sub i 1)) < c @ i)) vars)
  ;;

  let postcondition formulae =
    let intervals =
      List.map (fold_bexp (fun _ i (l, r) -> Int.(min i l, max i r)) (0, 0)) formulae
    in
    let min, max =
      List.fold_left
        (fun (gmin, gmax) (lmin, lmax) -> Int.(min gmin lmin, max gmax lmax))
        (0, 0)
        intervals
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
    And expanded_formulae
  ;;

  let precondition post = map_ind_bexp (fun _ i -> i - 1) post

  let make formulae =
    let post = postcondition formulae in
    let cond = inductive_step formulae in
    let pre = precondition post in
    pre, cond, post
  ;;
end
