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

let rec create_dir fn =
  if not (Sys.file_exists fn)
  then (
    let parent_dir = Filename.dirname fn in
    create_dir parent_dir;
    Sys.mkdir fn 0o755)
;;

let write_file ~filename f =
  let file = open_out filename in
  Fun.protect
    ~finally:(fun () ->
      flush file;
      close_out file)
    (fun () -> f file)
;;

type rounding =
  | Near
  | Floor
  | Ceil

let of_rounding = function
  | Near -> modulo_near
  | Floor -> modulo_floor
  | Ceil -> modulo_ceil
;;

let parse_rounding = function
  | "near" -> Near
  | "floor" -> Floor
  | "ceil" -> Ceil
  | s -> invalid_arg (Printf.sprintf "parsing rounding, unexpected string: %s" s)
;;

type 'n generation_config =
  { steps : int
  ; horizon : 'n
  }

type 'n processing_config =
  { print_svgbob : bool
  ; print_cadp : bool
  ; print_timed_cadp : 'n option
  ; debug : bool
  ; gen : 'n generation_config
  ; directory : string
  ; rounding : rounding
  }

let generate_trace ~config ~session system_spec order_hints clocks tasks i =
  let strategy = ST.Solution.refuse_empty random_strat in
  let env = A.of_spec ~debug:config.debug system_spec in
  let trace, cut =
    A.gen_trace strategy env
    |> A.Trace.take ~steps:config.gen.steps
    |> A.Trace.until ~horizon:config.gen.horizon
  in
  let trace = A.Trace.persist ~size_hint:config.gen.steps trace in
  let deadlock = Iter.length trace <> config.gen.steps && not !cut in
  Printf.printf "trace deadlocked: %b\n" deadlock;
  let basename = Printf.sprintf "%s/%i" config.directory i in
  if config.print_svgbob
  then
    write_file ~filename:(Printf.sprintf "%s.svgbob" basename) (fun trace_file ->
      Export.trace_to_vertical_svgbob
        ~numbers:false
        ~tasks
        session
        clocks
        (Format.formatter_of_out_channel trace_file)
        trace);
  if config.print_cadp
  then
    write_file ~filename:(Printf.sprintf "%s.cadp" basename) (fun trace_file ->
      Export.trace_to_cadp session (Format.formatter_of_out_channel trace_file) trace);
  Option.iter
    (fun step ->
       let modulo = of_rounding config.rounding in
       write_file ~filename:(Printf.sprintf "%s.tcadp" basename) (fun trace_file ->
         Export.trace_to_timed_cadp
           session
           (modulo ~divisor:step)
           order_hints
           (Format.formatter_of_out_channel trace_file)
           trace))
    config.print_timed_cadp;
  trace
;;

let trace_to_chains chain trace =
  let semantics = Earliest in
  let chain_instances, _ = trace_to_chain semantics chain (A.Trace.to_iter trace) in
  chain_instances
;;

module Opt = Mrtccsl.Optimization.Order.Make (String)

let run_simulation ~config ~bin_size ~processor (name, m, tasks, chains) =
  let spec = Mrtccsl.Ccsl.Language.Module.flatten m in
  let spec = Opt.optimize spec in
  let order_hints = Ccsl.MicroStep.derive_order spec.logical in
  let clocks = Ccsl.Language.Specification.clocks spec in
  let prefix = Filename.concat config.directory name in
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
  let open FnCh.S.Session in
  let session = create () in
  let spec = with_spec session spec in
  let chains =
    List.map (fun (name, chain) -> name, Chain.map (to_offset session) chain) chains
  in
  let tasks = List.map (Automata.Export.map_task @@ to_offset session) tasks in
  let traces =
    processor
    @@ generate_trace
         ~config:{ config with directory = prefix }
         ~session
         spec
         order_hints
         clocks
         tasks
  in
  let process_chain (chain_name, chain) =
    (* Format.printf
      "%a\n"
      (Chain.pp (fun fmt v -> Format.pp_print_string fmt (of_offset session v)))
      chain; *)
    let chain_instances =
      traces
      |> List.map (trace_to_chains chain)
      |> List.map Dynarray.to_iter
      |> List.fold_left Iter.append Iter.empty
    in
    let spans_to_consider = Chain.spans_of_interest chain in
    let categories = Chain.sampling_clocks chain in
    let make_histogram span =
      let module S = Stats.Make (String) (Number.Rational) in
      let misses_into_category map =
        List.to_string
          ~sep:"_"
          (fun sample ->
             let missed = CMap.find_opt sample map in
             let missed = Option.value ~default:0 missed in
             Printf.sprintf "%s_%i" (of_offset session sample) missed)
          categories
      in
      let reaction_times =
        Iter.map
          (fun ({ misses; _ } as chain : chain_instance) ->
             misses_into_category misses, reaction_time_of_span chain span)
          chain_instances
      in
      let histogram =
        S.histogram
          (fun x ->
             let _, closest_whole, _ = modulo_floor x ~divisor:bin_size in
             (* Printf.printf "%s\n" (Number.Rational.to_string closest_whole); *)
             closest_whole)
          reaction_times
      in
      write_file
        ~filename:
          (Printf.sprintf
             "%s/%s_%s_%s_reaction_time_hist.csv"
             prefix
             chain_name
             (of_offset session (fst span))
             (of_offset session (snd span)))
        (fun data_file -> S.to_csv (Format.formatter_of_out_channel data_file) histogram)
    in
    List.iter make_histogram spans_to_consider
  in
  List.iter process_chain chains
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

let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s
;;

let parse_chain_file filename =
  let content = read_whole_file filename in
  let chains = String.split ~by:"\n" content in
  chains |> List.filter (not << String.is_empty) |> List.map Chain.parse_with_name
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
  and print_cadp_trace = ref false
  and print_tcadp_trace = ref false
  and scale = ref ""
  and inspect_deadlock = ref false
  and directory = ref ""
  and chain_file = ref ""
  and tasks = ref ""
  and rounding = ref "near" in
  let speclist =
    [ "--traces", Arg.Set_int traces, "Number of traces to generate"
    ; "--cores", Arg.Set_int cores, "Number of cores to use"
    ; "--horizon", Arg.Set_float horizon, "Max time of simulation"
    ; "--steps", Arg.Set_int steps, "Max steps of simulation"
    ; "--tasks", Arg.Set_string tasks, "Tasks specification"
    ; "-o", Arg.Set_string directory, "Output directory path"
    ; ( "-fc"
      , Arg.Set_string chain_file
      , "Path to functional chain specifications, links are -> and ?" )
    ; "-bob", Arg.Set print_svgbob, "Print svgbob trace"
    ; "-cadp", Arg.Set print_cadp_trace, "Print CADP trace"
    ; "--scale", Arg.Set_string scale, "Set scale for histogram and timed CADP"
    ; "-tcadp", Arg.Set print_tcadp_trace, "Print CADP trace with time advances"
    ; ( "-inspect"
      , Arg.Set inspect_deadlock
      , "Collect and print debug information for deadlocked traces" )
    ; "-rounding", Arg.Set_string rounding, "near|floor|ceil"
    ]
  in
  let specification = ref "" in
  let _ = Arg.parse speclist (fun file -> specification := file) usage_msg in
  let recommended_cores = Stdlib.Domain.recommended_domain_count () in
  if !traces < 1 then invalid_arg "number of traces should be positive";
  if !cores < 1 then invalid_arg "number of cores should be positive";
  if !steps < 1 then invalid_arg "number of steps should be positive";
  if !horizon <= 0.0 then invalid_arg "horizon should be positive";
  if !chain_file = "" then invalid_arg "empty chain filename";
  if String.is_empty !specification
  then invalid_arg "specification filepath cannot be empty";
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
            ~body:(fun v -> [ f v ])
            pool
            List.append
            []))
    else
      fun f ->
        Iter.int_range ~start:0 ~stop:(Int.pred !traces)
        |> Iter.map f
        |> Iter.fold (Fun.flip List.cons) []
  in
  Ocolor_format.prettify_formatter Format.std_formatter;
  let ast =
    Mrtccslparsing.Parse.from_file !specification
    |> Result.map_error (fun pp_e ->
      fun fmt -> Format.fprintf fmt "Parsing error: %a" pp_e)
    |> Result.unwrap ~msg:"Failed in parsing."
  in
  let functional_chains = parse_chain_file !chain_file in
  let name = Filename.basename !specification in
  let context, m, errors = Mrtccslparsing.Compile.into_module ast in
  if List.is_empty errors
  then (
    let scale = if !scale = "" then None else Some (of_decimal_string !scale) in
    let v2s =
      Mrtccslparsing.Compile.(
        function
        | Explicit v -> List.to_string ~sep:"." Fun.id v
        | Anonymous i -> Printf.sprintf "anon(%i)" i)
    in
    let m = Mrtccsl.Ccsl.Language.Module.map v2s v2s Fun.id v2s v2s Fun.id m in
    run_simulation
      ~processor
      ~bin_size:(Option.value ~default:(Number.Rational.from_pair (1, 1000)) scale)
      ~config:
        { debug = !inspect_deadlock
        ; print_svgbob = !print_svgbob
        ; print_cadp = !print_cadp_trace
        ; print_timed_cadp = (if !print_tcadp_trace then scale else None)
        ; gen = { horizon = of_float !horizon; steps = !steps }
        ; directory = !directory
        ; rounding = parse_rounding !rounding
        }
      (name, m, [], functional_chains))
  else (
    Mrtccslparsing.Compile.Context.pp Format.std_formatter context;
    List.iter (Mrtccslparsing.Compile.print_compile_error Format.std_formatter) errors;
    failwith "Compilation error.")
;;
