open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
module C = Halsoa.Examples.Make (Number.Rational)
open Number.Rational
open FnCh

let step = of_int 1 / of_int 1000

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
    let priotized, rest =
      List.partition (fun (l, _) -> A.L.cardinal (A.L.inter l priorities) > 0) candidates
    in
    if List.is_empty priotized then general_strategy rest else general_strategy priotized
  in
  f
;;

(*TODO: need to review if the priority strategy is really correct*)
let fifo_strategy priorities general_strategy =
  let queue = ref [] in
  let priorities = A.CMap.of_list priorities in
  let f candidates =
    let prioritized =
      !queue
      |> List.find_mapi (fun _ c ->
        match List.filter (fun (l, _) -> A.L.mem c l) candidates with
        | [] -> None
        | list -> Some list)
    in
    match
      Option.bind_or (Option.bind prioritized general_strategy) (fun _ ->
        general_strategy candidates)
    with
    | Some (label, _) as solution ->
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
      solution
    | None -> None
  in
  f
;;

let random_strat =
  A.Strategy.Solution.avoid_empty
  @@ A.Strategy.Solution.random_label
       (A.Strategy.Num.random_leap
          ~upper_bound:(of_int 1000)
          ~ceil:(round_up step)
          ~floor:(round_down step)
          ~rand:random)
;;

module LSet = Set.Make (A.L)

let prioritize_single candidates =
  let labels = LSet.of_list (List.map (fun (x, _) -> x) candidates) in
  let candidates =
    List.filter
      (fun (l, _) ->
         A.L.cardinal l <= 1
         ||
         let ps =
           A.L.to_list l
           |> List.powerset_nz
           |> List.filter_map (fun l' ->
             let l' = A.L.of_list l' in
             if A.L.equal l l' then None else Some l')
         in
         not
           (List.exists
              (fun sub -> LSet.mem sub labels && LSet.mem (A.L.diff l sub) labels)
              ps))
      candidates
  in
  candidates
;;

let parallel_reaction_times
      ~sem
      ?(with_partial = false)
      params
      dist
      system_spec
      func_chain_spec
      runs
  =
  let _, _, horizon = params in
  let start, finish = chain_start_finish_clocks func_chain_spec in
  let pool = Domainslib.Task.setup_pool ~num_domains:8 () in
  let body _ =
    let _, _, full_chains, partial_chains =
      FnCh.functional_chains ~sem params dist system_spec func_chain_spec
    in
    let full_reaction_times =
      FnCh.reaction_times [ start, finish ] (List.to_seq full_chains)
    in
    if with_partial
    then
      partial_chains
      |> List.to_seq
      |> Seq.map (fun (t : partial_chain) ->
        ( t.misses
        , [ start, finish ]
          |> List.to_seq
          |> Seq.map (fun (source, target) ->
            ( (source, target)
            , CMap.value ~default:horizon target t.trace - CMap.find source t.trace ))
          |> Hashtbl.of_seq ))
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

let rec create_dir fn =
  if not (Sys.file_exists fn)
  then (
    let parent_dir = Filename.dirname fn in
    create_dir parent_dir;
    Sys.mkdir fn 0o755)
;;

let generate_trace ~steps ~horizon directory dist system_spec tasks func_chain_spec i =
  let _ = Random.self_init () in
  let strategy candidates = (A.Strategy.Solution.refuse_empty random_strat) candidates in
  let basename = Printf.sprintf "%s/%i" directory i in
  let sem = Earliest
  and points_of_interest = points_of_interest func_chain_spec in
  let trace, _, chains, _ =
    FnCh.functional_chains
      ~sem
      (strategy, steps, horizon)
      dist
      system_spec
      func_chain_spec
  in
  let clocks = List.sort_uniq String.compare (Rtccsl.spec_clocks system_spec) in
  let _ =
    let trace_file = open_out (Printf.sprintf "./%s.svgbob" basename) in
    A.trace_to_vertical_svgbob ~numbers:false ~precision:2 ~tasks clocks trace_file trace;
    close_out trace_file
  in
  let trace_file = open_out (Printf.sprintf "%s.trace" basename) in
  (*TODO: decide on better *)
  let _ = Printf.fprintf trace_file "%s" (A.trace_to_csl trace) in
  let _ = close_out trace_file in
  let reactions = FnCh.reaction_times points_of_interest (List.to_seq chains) in
  reactions
;;

let parallel = false

let process_config ~pool ~directory ~traces ~horizon ~steps (name, dist, spec, tasks) =
  let prefix = Filename.concat directory name in
  let _ = print_endline prefix in
  let _ = create_dir prefix in
  let _ =
    print_endline
      (Rtccsl.show_specification
         Format.pp_print_string
         Format.pp_print_string
         Format.pp_print_string
         (fun state v ->
            let s = to_string v in
            Format.pp_print_string state s)
         spec)
  in
  let reaction_times =
    if parallel
    then
      Domainslib.Task.run pool (fun _ ->
        Domainslib.Task.parallel_for_reduce
          ~chunk_size:1
          ~start:0
          ~finish:traces
          ~body:(generate_trace ~steps ~horizon prefix dist spec tasks C.icteri_chain)
          pool
          Seq.append
          Seq.empty)
    else
      Seq.int_seq_inclusive (0, traces)
      |> Seq.map (generate_trace ~steps ~horizon prefix dist spec tasks C.icteri_chain)
      |> Seq.fold_left Seq.append Seq.empty
  in
  let points_of_interest = points_of_interest C.icteri_chain in
  let categories = categorization_points C.icteri_chain in
  let data_file = open_out (Printf.sprintf "%s/reaction_times.csv" prefix) in
  let _ =
    Printf.fprintf
      data_file
      "%s"
      (FnCh.reaction_times_to_csv categories points_of_interest reaction_times)
  in
  close_out data_file
;;

let () =
  (*TODO: add some argument checking*)
  let usage_msg = "sim_halsoa [-t <traces>] [-n <cores>] [-h <trace horizon>] <dir>" in
  let traces = ref 0
  and cores = ref 1
  and steps = ref 1000
  and horizon = ref 10_000.0 in
  let speclist =
    [ "-t", Arg.Set_int traces, "Number of traces to generate"
    ; "-c", Arg.Set_int cores, "Number of cores to use"
    ; "-h", Arg.Set_float horizon, "Max time of simulation"
    ; "-s", Arg.Set_int steps, "Max steps of simulation"
    ]
  in
  let directory = ref None in
  let _ = Arg.parse speclist (fun dir -> directory := Some dir) usage_msg in
  let pool = Domainslib.Task.setup_pool ~num_domains:!cores () in
  List.iter
    (process_config
       ~pool
       ~traces:!traces
       ~directory:(Option.get !directory)
       ~steps:!steps
       ~horizon:(of_float !horizon))
    C.icteri_configs
;;
