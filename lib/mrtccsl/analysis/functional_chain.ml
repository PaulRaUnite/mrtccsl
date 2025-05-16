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
    Printf.sprintf
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

  let points_of_interest chain =
    let _, sampling_links =
      List.fold_left
        (fun (prev, points) (rel, next) ->
           let points =
             match rel with
             | `Sampling -> points @ [ prev, next ]
             | _ -> points
           in
           next, points)
        (chain.first, [])
        chain.rest
    in
    chain_start_finish_clocks chain :: sampling_links
  ;;

  type semantics =
    | All
    | Earliest
    | Lastest
    | Randomized

  (*TODO: optimize*)
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
    let full_chains, dangling_chains = trace_to_chain sem chain trace in
    (* let _ =
      Printf.printf "There are %i dangling chains.\n" (List.length dangling_chains);
      Printf.printf
        "%s\n"
        (List.to_string ~sep:"\n" partial_chain_to_string dangling_chains)
    in *)
    trace, deadlock, full_chains, dangling_chains
  ;;

  let reaction_times pairs_to_compare chains =
    chains
    |> Seq.map (fun (t : chain_instance) ->
      ( t.misses
      , pairs_to_compare
        |> List.to_seq
        |> Seq.map
             N.(
               fun (source, target) ->
                 (source, target), CMap.find target t.trace - CMap.find source t.trace)
        |> Hashtbl.of_seq ))
  ;;

  let statistics category chains =
    let module IMap = Map.Make (Int) in
    chains
    |> Seq.fold_left
         (fun acc ({ misses; _ } : chain_instance) ->
            IMap.entry
              (Int.add 1)
              0
              (Option.value ~default:0 (CMap.find_opt category misses))
              acc)
         IMap.empty
    |> IMap.to_seq
  ;;

  let print_statistics category chains =
    let stats = statistics category chains in
    let total = Seq.fold_left (fun total (_, x) -> total + x) 0 stats |> Float.of_int in
    Printf.printf "%s | %f\n" (C.to_string category) total;
    print_endline
      (Seq.to_string
         ~sep:"\n"
         (fun (c, x) -> Printf.sprintf "%i | %f" c (Float.of_int x /. total))
         stats)
  ;;

  let reaction_times_to_string ~sep seq =
    Seq.to_string
      ~sep
      (fun (_, t) ->
         t
         |> Hashtbl.to_seq
         |> Seq.to_string (fun ((s, f), v) ->
           Printf.sprintf "(%s, %s) -> %s" (C.to_string s) (C.to_string f) (N.to_string v)))
      seq
  ;;

  let reaction_times_to_csv categories pairs_to_print seq =
    let buf = Buffer.create 128 in
    let _ =
      Printf.bprintf
        buf
        "%s\n"
        (List.to_string
           ~sep:","
           Fun.id
           (List.map C.to_string categories
            @ List.map
                (fun (f, s) -> Printf.sprintf "%s->%s" (C.to_string f) (C.to_string s))
                pairs_to_print))
    in
    let _ =
      Seq.iter
        (fun (misses, times) ->
           Printf.bprintf
             buf
             "%s\n"
             (List.to_string
                ~sep:","
                Fun.id
                (List.map
                   (fun h ->
                      let v = Option.value ~default:0 (CMap.find_opt h misses) in
                      Int.to_string v)
                   categories
                 @ List.map (fun k -> N.to_string (Hashtbl.find times k)) pairs_to_print)))
        seq
    in
    Buffer.contents buf
  ;;
end
