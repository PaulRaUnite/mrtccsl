(* open Prelude *)

(**
Priority order of specifications, from most to least. Decision taken in earlier specification canot be overwritten.
*)
(* type 'a order = 'a list list

module Automata (A : Simple.S) = struct
  let sync (strategy : A.Strategy.Solution.t) (specs : _ Rtccsl.specification order) : A.t =
    let memorize_decision (guard, trans, domain) =
      let decided = ref None in
      let guard now =
        let label, now' =
          match !decided with
          | Some sol -> sol
          | None ->
            let variants = guard now in
            let sol = Option.get (strategy variants) in
            decided := Some sol;
            sol
        in
        [ (label, A.I.(now' =-= now')); (A.L.empty, A.I.(now <-> now')) ]
      in
      let trans now sol =
        (match !decided with
         | Some dec -> if dec = sol then decided := None
         | None -> ());
        trans now sol
      in
      guard, trans, domain
    in
    let parallel_sync independent =
      List.fold_left A.sync A.empty (List.map A.of_spec independent)
    in
    let order_sync prev next =
      let prev = memorize_decision prev in
      let group = parallel_sync next in
      A.sync prev group
    in
    List.reduce_left order_sync parallel_sync specs
  ;;
end *)
