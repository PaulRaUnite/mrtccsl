open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
module S = FnCh.S
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
           Int.neg
           @@ Int.compare
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
(* let fifo_strategy priorities general_strategy =
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
;; *)

let random_strat =
  ST.Solution.avoid_empty
  @@ ST.Solution.random_label
       (ST.Num.random_leap
          ~upper_bound:(of_int 1000)
          ~ceil:(round_up step)
          ~floor:(round_down step)
          ~rand:random)
;;

(*
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
;; *)

let parallel_reaction_times
      ~sem
      ?(with_partial = false)
      params
      system_spec
      func_chain_spec
      runs
  =
  let _, _, horizon = params in
  let start, finish = chain_start_finish_clocks func_chain_spec in
  let pool = Domainslib.Task.setup_pool ~num_domains:8 () in
  let body _ =
    let session, _, _, full_chains, partial_chains =
      FnCh.functional_chains ~sem params system_spec func_chain_spec
    in
    let full_reaction_times =
      FnCh.reaction_times session [ start, finish ] (Iter.of_dynarray full_chains)
    in
    if with_partial
    then
      partial_chains
      |> Iter.of_array
      |> Iter.flat_map Queue.to_iter
      |> Iter.map (fun (t : partial_chain) ->
        ( t.misses
          |> A.CMap.to_seq
          |> Seq.map (fun (k, v) -> S.Session.of_offset session k, v)
          |> Hashtbl.of_seq
        , [ start, finish ]
          |> List.to_seq
          |> Seq.map (fun (source, target) ->
            ( (source, target)
            , CMap.value ~default:horizon (S.Session.to_offset session target) t.trace
              - CMap.find (S.Session.to_offset session source) t.trace ))
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
      Iter.append
      Iter.empty)
;;

let rec create_dir fn =
  if not (Sys.file_exists fn)
  then (
    let parent_dir = Filename.dirname fn in
    create_dir parent_dir;
    Sys.mkdir fn 0o755)
;;

let generate_trace
      ~print_svgbob
      ~print_trace
      ?(debug = false)
      ~steps
      ~horizon
      directory
      system_spec
      tasks
      func_chain_spec
      i
  =
  let strategy = ST.Solution.refuse_empty random_strat in
  let basename = Printf.sprintf "%s/%i" directory i in
  let sem = Earliest
  and points_of_interest = points_of_interest func_chain_spec in
  let session, trace, deadlock, chains, _ =
    FnCh.functional_chains
      ~debug
      ~sem
      (strategy, steps, horizon)
      system_spec
      func_chain_spec
  in
  Printf.printf "trace deadlocked: %b\n" deadlock;
  if print_svgbob
  then (
    let clocks =
      List.sort_uniq String.compare (Language.Specification.clocks system_spec)
    in
    let trace_file = open_out (Printf.sprintf "./%s.svgbob" basename) in
    Export.trace_to_vertical_svgbob
      ~numbers:false
      ~tasks
      session
      clocks
      (Format.formatter_of_out_channel trace_file)
      trace;
    close_out trace_file);
  if print_trace
  then (
    let trace_file = open_out (Printf.sprintf "%s.trace" basename) in
    Export.trace_to_csl session (Format.formatter_of_out_channel trace_file) trace;
    close_out trace_file);
  let reactions =
    FnCh.reaction_times session points_of_interest (Iter.of_dynarray chains)
  in
  Iter.persistent reactions
;;

module Opt = Mrtccsl.Optimization.Order.Make (String)

let process_config
      ~bin_size
      ~debug
      ~print_svgbob
      ~print_trace
      ~directory
      ~processor
      ~horizon
      ~steps
      (name, m, tasks, chain)
  =
  let spec = Mrtccsl.Ccsl.Language.Module.flatten m in
  let spec = Opt.optimize spec in
  let prefix = Filename.concat directory name in
  let _ = print_endline prefix in
  let _ = create_dir prefix in
  let _ =
    print_endline
      (Language.Specification.show
         Format.pp_print_string
         Format.pp_print_string
         Format.pp_print_string
         Format.pp_print_string
         Format.pp_print_string
         (fun state v ->
            let s = to_string v in
            Format.pp_print_string state s)
         spec)
  in
  let reaction_times =
    processor
    @@ generate_trace
         ~debug
         ~print_svgbob
         ~print_trace
         ~steps
         ~horizon
         prefix
         spec
         tasks
         chain
  in
  let points_of_interest = points_of_interest chain in
  let categories = categorization_points chain in
  let data_file = open_out (Printf.sprintf "%s/reaction_times.csv" prefix) in
  let _ =
    FnCh.reaction_times_to_csv categories points_of_interest data_file reaction_times
  in
  close_out data_file;
  let data_file = open_out (Printf.sprintf "%s/reaction_time_hist.csv" prefix) in
  let start, finish = chain_start_finish_clocks chain in
  let module S = Stats.Make (String) (Number.Rational) in
  let sample_points = categorization_points chain in
  let misses_into_category map =
    List.to_string
      ~sep:"_"
      (fun sample ->
         let missed = Hashtbl.find_opt map sample in
         let missed = Option.value ~default:0 missed in
         Printf.sprintf "%s_%i" sample missed)
      sample_points
  in
  let reaction_times =
    Iter.map
      (fun (misses, reaction_time) ->
         misses_into_category misses, Hashtbl.find reaction_time (start, finish))
      reaction_times
  in
  let histogram = S.histogram ~bin_size reaction_times in
  S.to_csv (Format.formatter_of_out_channel data_file) histogram;
  close_out data_file
;;

let parse_tasks s =
  let names = String.split ~by:"," s in
  List.map
    (fun name ->
       ( name
       , Printf.sprintf "%s.r" name
       , Printf.sprintf "%s.s" name
       , Printf.sprintf "%s.f" name
       , Printf.sprintf "%s.d" name ))
    names
;;

let () =
  let _ = Random.self_init () in
  let usage_msg =
    "simulate [--traces <traces>] [--cores <cores>] [--horizon <trace horizon>] [-bob] \
     [-cadp] [--tasks <tasks>] <specification> -o <dir> -fc <functional chain>"
  in
  let traces = ref 1
  and cores = ref 1
  and steps = ref 1000
  and horizon = ref 10_000.0
  and print_svgbob = ref false
  and print_trace = ref false
  and inspect_deadlock = ref false
  and directory = ref ""
  and chain = ref ""
  and tasks = ref "" in
  let speclist =
    [ "--traces", Arg.Set_int traces, "Number of traces to generate"
    ; "--cores", Arg.Set_int cores, "Number of cores to use"
    ; "--horizon", Arg.Set_float horizon, "Max time of simulation"
    ; "--steps", Arg.Set_int steps, "Max steps of simulation"
    ; "--tasks", Arg.Set_string tasks, "Tasks specification"
    ; "-o", Arg.Set_string directory, "Output directory path"
    ; "-fc", Arg.Set_string chain, "Functional chain specification, links are -> and ?"
    ; "-bob", Arg.Set print_svgbob, "Print svgbob trace"
    ; "-cadp", Arg.Set print_trace, "Print CADP trace"
    ; ( "-inspect"
      , Arg.Set inspect_deadlock
      , "Collect and print debug information for deadlocked traces" )
    ]
  in
  let specification = ref "" in
  let _ = Arg.parse speclist (fun file -> specification := file) usage_msg in
  let recommended_cores = Stdlib.Domain.recommended_domain_count () in
  if !traces < 1 then invalid_arg "number of traces should be positive";
  if !cores < 1 then invalid_arg "number of cores should be positive";
  if !steps < 1 then invalid_arg "number of steps should be positive";
  if !horizon <= 0.0 then invalid_arg "horizon should be positive";
  if !chain = "" then invalid_arg "empty chain";
  if String.is_empty !specification
  then invalid_arg "specification filepath cannot be emtpy";
  if String.is_empty !directory then invalid_arg "output directory path cannot be emtpy";
  let processor =
    if !cores <> 1
    then (
      let pool =
        Domainslib.Task.setup_pool ~num_domains:(Int.min !cores recommended_cores) ()
      in
      fun f ->
        Domainslib.Task.run pool (fun _ ->
          Domainslib.Task.parallel_for_reduce
            ~chunk_size:1
            ~start:0
            ~finish:(Int.pred !traces)
            ~body:f
            pool
            Iter.append
            Iter.empty))
    else
      fun f ->
        Iter.int_range ~start:0 ~stop:(Int.pred !traces)
        |> Iter.map f
        |> Iter.fold Iter.append Iter.empty
  in
  Ocolor_format.prettify_formatter Format.std_formatter;
  let ast =
    Mrtccslparsing.Parse.from_file !specification
    |> Result.map_error (fun pp_e ->
      fun fmt -> Format.fprintf fmt "Parsing error: %a" pp_e)
    |> Result.unwrap ~msg:"Failed in parsing."
  in
  let functional_chain = parse_chain !chain in
  let name = Filename.basename !specification in
  let context, m, errors = Mrtccslparsing.Compile.into_module ast in
  if List.is_empty errors
  then (
    let v2s =
      Mrtccslparsing.Compile.(
        function
        | Explicit v -> List.to_string ~sep:"." Fun.id v
        | Anonymous i -> Printf.sprintf "anon(%i)" i)
    in
    let m = Mrtccsl.Ccsl.Language.Module.map v2s v2s Fun.id v2s v2s Fun.id m in
    process_config
      ~processor
      ~bin_size:(Number.Rational.from_pair (1, 10))
      ~debug:!inspect_deadlock
      ~print_svgbob:!print_svgbob
      ~print_trace:!print_trace
      ~directory:!directory
      ~steps:!steps
      ~horizon:(of_float !horizon)
      (name, m, [], functional_chain))
  else (
    Mrtccslparsing.Compile.Context.pp Format.std_formatter context;
    List.iter (Mrtccslparsing.Compile.print_compile_error Format.std_formatter) errors;
    failwith "Compilation error.")
;;
