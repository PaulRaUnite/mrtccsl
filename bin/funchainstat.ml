open Mrtccsl
open Prelude
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
open Number.Rational

let step = of_int 1 / of_int 10

let priority_strategy priorities general_strategy =
  let priorities = A.L.of_list priorities in
  let f candidates =
    let candidates =
      List.stable_sort
        (fun (x, _) (y, _) ->
           -Int.compare
              (A.L.cardinal (A.L.inter x priorities))
              (A.L.cardinal (A.L.inter y priorities)))
        candidates
    in
    let priotized, _ =
      List.partition (fun (l, _) -> A.L.cardinal (A.L.inter l priorities) > 0) candidates
    in
    if List.is_empty priotized
    then general_strategy candidates
    else general_strategy priotized
  in
  f
;;

let fifo_strategy priorities general_strategy =
  let queue = ref [] in
  let priorities = A.CMap.of_list priorities in
  let f candidates =
    (* let _ = Format.printf "queue: %s\n" (List.to_string Fun.id !queue) in *)
    let prioritized =
      !queue
      |> List.find_mapi (fun i c ->
        match List.filter (fun (l, _) -> A.L.mem c l) candidates with
        | [] -> None
        | list -> Some list)
    in
    match
      Option.bind_or (Option.bind prioritized general_strategy) (fun _ ->
        general_strategy candidates)
    with
    | Some (label, now) as solution ->
      let _ =
        A.CMap.iter
          (fun r s ->
             if A.L.mem r label then queue := List.append !queue [ s ];
             if A.L.mem s label
             then (
               let _, new_queue =
                 List.map_inplace_or_drop (fun x -> if x = s then `Drop else `Skip) !queue
               in
               queue := new_queue))
          priorities
      in
      (* let _ = print_endline (A.solution_to_string (label, now)) in *)
      solution
    | None -> None
  in
  f
;;

let random_strat =
  A.Strategy.random_label
    ~avoid_empty:true
    10
    (A.Strategy.random_leap (of_int 100) (round_up step) (round_down step) random)
;;

let fast_strat =
  A.Strategy.random_label 10
  @@ A.Strategy.fast (A.I.make_include (of_int 0) (of_int 10)) (round_down step)
;;

let one = of_int 1
let two = of_int 2
let hundred = of_int 100
let half = Rational.(of_int 1 / of_int 2)

let parallel_reaction_times
      ?(with_partial = false)
      params
      system_spec
      func_chain_spec
      runs
  =
  let _, _, horizon = params in
  let start, finish = FnCh.chain_start_finish func_chain_spec in
  let pool = Domainslib.Task.setup_pool ~num_domains:8 () in
  let body _ =
    let _, _, full_chains, partial_chains =
      FnCh.functional_chains params system_spec func_chain_spec
    in
    let full_reaction_times =
      FnCh.reaction_times start finish (List.to_seq full_chains)
    in
    if with_partial
    then
      partial_chains
      |> List.to_seq
      |> Seq.map (fun c -> horizon - A.CMap.find start FnCh.(c.trace))
    else full_reaction_times
  in
  Domainslib.Task.run pool (fun _ ->
    Domainslib.Task.parallel_for_reduce
      ~chunk_size:1
      ~start:0
      ~finish:runs
      ~body
      pool
      Seq.append
      Seq.empty)
;;

let () =
  let _ = Random.init 82763452 in
  let system_spec =
    List.map (Rtccsl.map_time_const of_int) Rtccsl.Examples.SimpleControl.no_resource_constraint
  in
  let func_chain_spec =
    FnCh.
      { first = "s.t"
      ; rest =
          [ `Causality, "s.s"
          ; `Causality, "s.f"
          ; `Causality, "c.s"
          ; `Causality, "c.f"
          ; `Sampling, "a.s"
          ; `Causality, "a.f"
          ]
      }
  in
  let strategy =
    fifo_strategy
      [ "s.r", "s.s"; "a.r", "a.s"; "c.r", "c.s" ]
      (priority_strategy [ "s.s"; "c.s"; "a.s" ] random_strat)
  in
  let steps = 1_000 in
  let horizon = of_int 1_000 in
  let massive = false in
  let reactions =
    if massive
    then
      parallel_reaction_times
        ~with_partial:false
        (strategy, steps, horizon)
        system_spec
        func_chain_spec
        100
    else (
      let trace, deadlock, chains, _ =
        FnCh.functional_chains (strategy, steps, horizon) system_spec func_chain_spec
      in
      let chains = List.to_seq chains in
      let start, finish = FnCh.chain_start_finish func_chain_spec in
      let reactions = FnCh.reaction_times start finish chains in
      let _ = Format.printf "deadlock: %b\n" deadlock in
      let svgbob_str =
        A.trace_to_svgbob
          ~numbers:true
          ~precision:2
          ~tasks:Rtccsl.Macro.[ task_clocks "s"; task_clocks "c"; task_clocks "a" ]
          (List.sort_uniq String.compare (Rtccsl.spec_clocks system_spec))
          trace
      in
      let _ =
        let trace_file = open_out "./trace.txt" in
        output_string trace_file svgbob_str;
        close_out trace_file
      in
      let _ =
        Format.printf
          "chains:\n%s\n"
          (Seq.to_string
             ~sep:"\n"
             (FnCh.CMap.to_string String.to_string to_string)
             chains);
        Format.printf "reaction times: %s\n" (Seq.to_string to_string reactions)
      in
      let trace_file = open_out "./cadp_trace.txt" in
      let _ = Printf.fprintf trace_file "%s" (A.trace_to_csl trace) in
      let _ = close_out trace_file in
      reactions)
  in
  let data_file = open_out "./plots/data/reaction_times.txt" in
  let _ = Printf.fprintf data_file "%s" (FnCh.reaction_times_to_string reactions) in
  close_out data_file
;;
