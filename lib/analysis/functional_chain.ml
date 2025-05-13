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

  type chain_instance =
    { trace : N.t CMap.t
    ; misses : int CMap.t
    }

  type partial_chain =
    { trace : N.t CMap.t
    ; targets : int CMap.t
    ; misses : int CMap.t
    }

  let partial_chain_to_string chain =
    Format.sprintf
      "trace: %s targets: %s misses: %s"
      (CMap.to_string C.to_string N.to_string chain.trace)
      (CMap.to_string C.to_string Int.to_string chain.targets)
      (CMap.to_string C.to_string Int.to_string chain.misses)
  ;;

  let instructions chain_spec : (C.t * instruction) list =
    let init = chain_spec.first, (`New : instruction) in
    let rest_seq = chain_spec.rest |> List.map (fun (x, y) -> y, (x :> instruction)) in
    init :: rest_seq
  ;;

  let chain_start_finish_clocks chain =
    ( chain.first
    , Option.value
        ~default:chain.first
        (Option.map (fun (_, c) -> c) (List.last chain.rest)) )
  ;;

  type semantics =
    | All
    | Earliest
    | Lastest
    | Randomized

  let consume_label
        ?(sem = All)
        instructions
        (full_chains, partial_chains, counters)
        (label, now)
    =
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
    (* let dropped = ref 0 in *)
    let execute_instruction (partial_chains, index) (c, instr) =
      let partial_chain =
        if A.L.mem c label
        then (
          match instr with
          | `New ->
            let targets = targets_from index in
            List.append
              partial_chains
              [ { trace = CMap.singleton c now; targets; misses = CMap.empty } ]
          | `Causality ->
            partial_chains
            |> List.map (fun chain ->
              match CMap.find_opt c chain.targets with
              | Some target ->
                let counter = Array.get counters index in
                if target = counter
                then
                  { trace = CMap.add c now chain.trace
                  ; targets = chain.targets
                  ; misses = chain.misses
                  }
                else chain
              | None -> chain)
          | `Sampling ->
            let targets = targets_from index in
            let candidates =
              List.filter_mapi
                (fun i chain ->
                   if CMap.cardinal chain.trace = index then Some i else None)
                partial_chains
            in
            if List.is_empty candidates
            then partial_chains
            else (
              let to_modify, to_drop =
                match sem with
                | All -> candidates, []
                | Earliest ->
                  let first, rest = List.first_partition candidates in
                  Option.to_list first, rest
                | Lastest ->
                  let last, rest = List.last_partition candidates in
                  Option.to_list last, rest
                | Randomized ->
                  let index =
                    Random.int_in_range ~min:0 ~max:(List.length candidates - 1)
                  in
                  let el = List.nth candidates index in
                  [ el ], List.drop_nth candidates index
              in
              List.filter_mapi
                (fun i chain ->
                   if List.mem i to_modify
                   then
                     Some
                       { trace = CMap.add c now chain.trace
                       ; targets
                       ; misses = chain.misses
                       }
                   else if List.mem i to_drop
                   then
                     (* dropped := !dropped + 1; *)
                     None
                   else Some chain)
                partial_chains))
        else partial_chains
      in
      partial_chain, index + 1
    in
    let partial_chains, _ =
      Array.fold_left execute_instruction (partial_chains, 0) instructions
    in
    let partial_chains =
      List.map
        (fun { trace; targets; misses } ->
           let misses =
             A.L.fold
               (fun k misses ->
                  if not (CMap.mem k trace)
                  then CMap.entry (fun v -> v + 1) 0 k misses
                  else misses)
               label
               misses
           in
           { trace; targets; misses })
        partial_chains
    in
    let new_full, rest =
      List.partition (fun c -> CMap.cardinal c.trace = len) partial_chains
    in
    let new_full =
      List.map (fun chain -> { trace = chain.trace; misses = chain.misses }) new_full
    in
    (* let _ = Printf.printf "dropped: %d\n" !dropped in *)
    List.append full_chains new_full, rest, counters
  ;;

  let trace_to_chain sem chain trace =
    let instructions = Array.of_list (instructions chain) in
    let len_instr = Array.length instructions in
    let full_chains, dangling_chains, _ =
      Seq.fold_left
        (consume_label ~sem instructions)
        ([], [], Array.make len_instr 0)
        trace
    in
    full_chains, dangling_chains
  [@@inline]
  ;;

  let functional_chains
        ?(sem = All)
        (s, n, time)
        (system_spec : (A.clock, A.param, A.num) Rtccsl.specification)
        (chain : chain)
    =
    let automaton = A.of_spec system_spec in
    let trace, deadlock = A.gen_trace_until s n time automaton in
    let full_chains, dangling_chains = trace_to_chain sem chain (List.to_seq trace) in
    (* let _ =
      Format.printf "There are %i dangling chains.\n" (List.length dangling_chains);
      Format.printf
        "%s\n"
        (List.to_string ~sep:"\n" partial_chain_to_string dangling_chains)
    in *)
    trace, deadlock, full_chains, dangling_chains
  ;;

  let reaction_times source target chains =
    chains
    |> Seq.map (fun (t : chain_instance) ->
      t.misses, N.(CMap.find target t.trace - CMap.find source t.trace))
  ;;

  let reaction_times_to_string ~sep seq =
    Seq.to_string ~sep (fun (_, t) -> N.to_string t) seq
  ;;

  let reaction_times_to_csv header seq =
    let reactions = Array.of_seq seq in
    let _ = Array.sort (fun (_, t1) (_, t2) -> N.compare t1 t2) reactions in
    let buf = Buffer.create 128 in
    let _ = List.iter (fun h -> Printf.bprintf buf "%s," (C.to_string h)) header in
    let _ = Buffer.add_string buf "x\n" in
    let _ =
      Array.iter
        (fun (misses, t) ->
           List.iter
             (fun h ->
                let v = Option.value ~default:0 (CMap.find_opt h misses) in
                Printf.bprintf buf "%i," v)
             header;
           Printf.bprintf buf "%s\n" (N.to_string t))
        reactions
    in
    Buffer.contents buf
  ;;
end
