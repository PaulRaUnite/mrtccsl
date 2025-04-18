open Prelude

module Make (C : Automata.Simple.ID) (N : Automata.Simple.Num) = struct
  module A = Automata.Simple.Make (C) (N)
  module CMap = Map.Make (C)

  type relation =
    [ `Causality
    | `Sampling
    ]

  type chain =
    { first : C.t
    ; rest : (relation * C.t) list
    }

  type instruction =
    [ relation
    | `New
    ]

  type partial_chain =
    { trace : N.t CMap.t
    ; targets : int CMap.t
    }

  let partial_chain_to_string chain =
    Format.sprintf
      "trace: %s targets: %s"
      (CMap.to_string C.to_string N.to_string chain.trace)
      (CMap.to_string C.to_string Int.to_string chain.targets)
  ;;

  let instructions chain_spec : (C.t * instruction) list =
    let init = chain_spec.first, (`New : instruction) in
    let rest_seq = chain_spec.rest |> List.map (fun (x, y) -> y, (x :> instruction)) in
    init :: rest_seq
  ;;

  let chain_start_finish chain =
    ( chain.first
    , Option.value
        ~default:chain.first
        (Option.map (fun (_, c) -> c) (List.last chain.rest)) )
  ;;

  let consume_label instructions (full_chains, partial_chains, counters) (label, now) =
    let len = Array.length instructions in
    let targets_from i =
      let chain_target = Array.get counters i in
      let targets, _ =
        Seq.fold_lefti
          (fun (targets, met_sampling) j (c, instr) ->
             match met_sampling, instr with
             | false, `Causality when j > i -> CMap.add c chain_target targets, false
             | _, `Sampling when j > i -> targets, true
             | _ -> targets, met_sampling)
          (CMap.empty, false)
          (Array.to_seq instructions)
      in
      targets
    in
    let _ =
      Array.mapi_inplace
        (fun i current ->
           let c, _ = Array.get instructions i in
           let current = current + if A.L.mem c label then 1 else 0 in
           current)
        counters
    in
    let execute_instruction (partial_chains, index) (c, instr) =
      let partial_chain =
        if A.L.mem c label
        then (
          match instr with
          | `New ->
            let targets = targets_from index in
            List.append partial_chains [ { trace = CMap.singleton c now; targets } ]
          | `Causality ->
            List.map
              (fun chain ->
                 match CMap.find_opt c chain.targets with
                 | Some target ->
                   let counter = Array.get counters index in
                   if target = counter
                   then { trace = CMap.add c now chain.trace; targets = chain.targets }
                   else chain
                 | None -> chain)
              partial_chains
          | `Sampling ->
            let targets = targets_from index in
            List.map
              (fun chain ->
                 if CMap.cardinal chain.trace = index
                 then { trace = CMap.add c now chain.trace; targets }
                 else chain)
              partial_chains)
        else partial_chains
      in
      partial_chain, index + 1
    in
    let partial_chains, _ =
      Array.fold_left execute_instruction (partial_chains, 0) instructions
    in
    let new_full, rest =
      List.partition (fun c -> CMap.cardinal c.trace = len) partial_chains
    in
    let new_full = List.map (fun chain -> chain.trace) new_full in
    List.append full_chains new_full, rest, counters
  ;;

  let functional_chains
        (s, n, time)
        (system_spec : (A.clock, A.param, A.num) Rtccsl.specification)
        (chain : chain)
    =
    let automaton = A.of_spec system_spec in
    let trace, deadlock = A.gen_trace_until s n time automaton in
    let instructions = Array.of_list (instructions chain) in
    let len_instr = Array.length instructions in
    let full_chains, dangling_chains, _ =
      Seq.fold_left
        (consume_label instructions)
        ([], [], Array.make len_instr 0)
        (List.to_seq trace)
    in
    (* let _ =
      Format.printf "There are %i dangling chains.\n" (List.length dangling_chains);
      Format.printf
        "%s\n"
        (List.to_string ~sep:"\n" partial_chain_to_string dangling_chains)
    in *)
    trace, deadlock, full_chains, dangling_chains
  ;;

  let reaction_times source target chains =
    chains |> Seq.map (fun m -> N.(CMap.find target m - CMap.find source m))
  ;;

  let reaction_times_to_string seq = Seq.to_string ~sep:"\n" N.to_string seq
end
