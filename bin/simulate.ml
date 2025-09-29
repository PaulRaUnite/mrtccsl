open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
module S = FnCh.S
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
    let prioritized, rest =
      List.partition (fun (l, _) -> A.L.cardinal (A.L.inter l priorities) > 0) candidates
    in
    if List.is_empty prioritized
    then general_strategy rest
    else general_strategy prioritized
  in
  f
;;

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

type 'n config =
  { steps : int
  ; horizon : 'n option
  ; output_dir : string
  ; cores : int
  ; traces : int
  }

module Opt = Mrtccsl.Optimization.Order.Make (String)

let read_whole_file filename =
  (* open_in_bin works correctly on Unix and Windows *)
  let ch = open_in_bin filename in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch;
  s
;;

open Cmdliner
open Cmdliner.Term.Syntax
open Common

let recommended_cores = Stdlib.Domain.recommended_domain_count ()

let spec_file_arg =
  Arg.(
    required
    (* TODO: make it possible to use stdin (need modifications to parsing and its error reporting) *)
    & pos 0 (some non_dir_file) None
    & info [] ~doc:"Path to specification file." ~docv:"SPEC")
;;

let output_dir_arg =
  Arg.(
    required
    & opt (some string) None
    & info [ "o"; "output" ] ~doc:"Path to output directory." ~docv:"OUT")
;;

let cores_arg =
  Arg.(
    value
    & opt int recommended_cores
    & info
        [ "c"; "cores" ]
        ~doc:"Number of cores (>= 1) that are used to generate traces."
        ~docv:"CORES")
;;

let traces_arg =
  Arg.(
    value
    & opt int 1
    & info [ "t"; "traces" ] ~doc:"Number of traces (>= 1) to be generated." ~docv:"CORES")
;;

let horizon_arg =
  Arg.(
    value
    & opt (some string) None
    & info
        [ "h"; "horizon" ]
        ~doc:
          "Maximum value in real-time that the simulation can reach. Has to be positive \
           non-null decimal number (any precision)."
        ~absent:"The trace is only limited by number of $(STEPS)."
        ~docv:"HORIZON")
;;

let steps_arg =
  Arg.(
    value
    & opt int 100_000
    & info
        [ "s"; "steps" ]
        ~doc:"Maximum number (>= 0) of steps in a trace."
        ~docv:"STEPS")
;;

let verify_config config =
  if config.cores < 1
  then
    failwithf
      "invalid value %i of CORES variable: has to be bigger or equal to one"
      config.cores
  else (
    match config.horizon with
    | Some horizon when Number.Rational.less_eq horizon Number.Rational.zero ->
      failwithf
        "invalid value %s of HORIZON variable: has to be positive non-zero decimal number"
        (Number.Rational.to_string horizon)
    | _ ->
      ();
      if config.steps < 0
      then
        failwithf
          "invalid value %i of STEPS variable: has to be non-negative integer"
          config.steps)
;;

let generate_trace ~session ~config clocks spec i =
  let strategy = ST.Solution.refuse_empty random_strat in
  let env = A.of_spec ~debug:false spec in
  let trace = A.gen_trace strategy env |> A.Trace.take ~steps:config.steps in
  let trace =
    match config.horizon with
    | Some horizon ->
      let trace, _ = A.Trace.until ~horizon trace in
      trace
    | None -> trace
  in
  let basename = Printf.sprintf "%s/%i" config.output_dir i in
  Sys.write_file ~filename:(Printf.sprintf "%s.trace" basename) (fun ch ->
    FnCh.Export.write_csv session ch (List.map (S.Session.to_offset session) clocks) trace)
;;

let simulate ~config m =
  verify_config config;
  let processor =
    if config.cores <> 1
    then (
      let pool =
        Domainslib.Task.setup_pool
          ~num_domains:(Int.min config.cores recommended_cores)
          ()
      in
      fun f ->
        Domainslib.Task.run pool (fun _ ->
          Domainslib.Task.parallel_for_reduce
            ~chunk_size:1
            ~start:0
            ~finish:(Int.pred config.traces)
            ~body:(fun v -> [ f v ])
            pool
            List.append
            []))
    else
      fun f ->
        Iter.int_range ~start:0 ~stop:(Int.pred config.traces)
        |> Iter.map f
        |> Iter.fold (Fun.flip List.cons) []
  in
  let _ = Random.self_init () in
  let spec = Mrtccsl.Ccsl.Language.Module.flatten m in
  let spec = Opt.optimize spec in
  let clocks = Ccsl.Language.Specification.clocks spec in
  let _ = print_endline config.output_dir in
  let _ = Sys.create_dir config.output_dir in
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
  ignore @@ processor @@ generate_trace ~session ~config clocks spec
;;

let cmd =
  Cmd.v (Cmd.info "simulate" ~version ~doc:"Simulate a CCSL+ specification.")
  @@ Term.ret
  @@ let+ specification = spec_file_arg
     and+ output_dir = output_dir_arg
     and+ cores = cores_arg
     and+ horizon = horizon_arg
     and+ steps = steps_arg
     and+ traces = traces_arg in
     Ocolor_format.prettify_formatter Format.std_formatter;
     let ast =
       Mrtccslparsing.Parse.from_file specification
       |> Result.map_error (fun pp_e ->
         fun fmt -> Format.fprintf fmt "Parsing error: %a" pp_e)
       |> Result.unwrap ~msg:"Failed in parsing."
     in
     let context, m, errors = Mrtccslparsing.Compile.into_module ast in
     if not (List.is_empty errors)
     then (
       Mrtccslparsing.Compile.Context.pp Format.std_formatter context;
       List.iter (Mrtccslparsing.Compile.print_compile_error Format.std_formatter) errors;
       failwith "Compilation error.")
     else (
       let v2s =
         Mrtccslparsing.Compile.(
           function
           | Explicit v -> List.to_string ~sep:"." Fun.id v
           | Anonymous i -> Printf.sprintf "anon(%i)" i)
       in
       let m = Mrtccsl.Ccsl.Language.Module.map v2s v2s Fun.id v2s v2s Fun.id m in
       let horizon = Option.map Number.Rational.of_decimal_string horizon in
       try
         `Ok (Ok (simulate ~config:{ cores; output_dir; horizon; steps; traces } m))
       with
       | Failure s -> `Error (false, s))
;;

let main () = Cmd.eval_result cmd
