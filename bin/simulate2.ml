open Common
open Mrtccsl
open Prelude

module Trace =
  Common.Trace.MakeIO (Number.Rational) (STS.Interpretation.Diagram.VarMap.Label)

open Number.Rational

let diagram_leap ~upper_bound ~rounding_error cond =
  let open Backend.Machine.Diagram.Simulation.RI in
  let left_bound = Option.value ~default:zero (left_bound_opt cond) in
  let cond =
    if is_right_unbound cond
    then inter cond (left_bound =-= left_bound + upper_bound)
    else cond
  in
  let x, y =
    match cond with
    | Bound (Include x, Include y) -> x, y
    | Bound (Exclude x, Include y) -> round_up rounding_error x y, y
    | Bound (Include x, Exclude y) -> x, round_down rounding_error x y
    | Bound (Exclude x, Exclude y) ->
      round_up rounding_error x y, round_down rounding_error x y
    | _ -> invalid_arg "random on infinite interval is not supported"
  in
  random x y
;;

type 'n config =
  { steps : int
  ; horizon : 'n option
  ; output_dir : string
  ; cores : int
  ; traces : int
  ; rounding_error : 'n
  ; default_upper_bound : 'n
  }

open Cmdliner
open Cmdliner.Term.Syntax
open Aux

let generate_trace ~config clocks repr i =
  let strategy =
    diagram_leap
      ~rounding_error:config.rounding_error
      ~upper_bound:config.default_upper_bound
  in
  let trace = Backend.Machine.Diagram.Simulation.gen_trace strategy repr in
  let trace, was_cut =
    match config.horizon with
    | Some horizon -> Trace.until ~horizon trace
    | None -> trace, ref false
  in
  let size = ref 0 in
  let monitor_size i x =
    size := Int.succ i;
    x
  in
  let trace = Seq.mapi monitor_size trace in
  let basename = Printf.sprintf "%s/%i" config.output_dir i in
  let _ =
    Sys.write_file ~filename:(Printf.sprintf "%s.trace" basename) (fun ch ->
      Trace.CSV.write ch clocks trace)
  in
  let deadlocked = if !was_cut then false else !size < config.steps in
  Printf.printf "deadlocked: %b, was_cut: %b, size: %i\n" deadlocked !was_cut !size
;;

(* if deadlocked then print_endline @@ A.to_string repr *)

module Opt = Mrtccsl.Optimization.Order.Make (String)

let simulate ~config m =
  let processor =
    if config.cores <> 1
    then (
      let pool =
        Domainslib.Task.setup_pool
          ~num_domains:(Int.min config.cores Simulate.recommended_cores)
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
  let spec = Mrtccsl.CCSL.Language.Module.flatten m in
  let spec = Opt.optimize spec in
  let clocks = CCSL.Language.Specification.clocks spec in
  let _ = print_endline config.output_dir in
  let _ = Sys.create_dir config.output_dir in
  let _ =
    print_endline
      (CCSL.Language.Specification.show
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
  let simulations =
    Array.of_list
    @@ Backend.Machine.Diagram.Simulation.sim_of_spec ~instances:config.traces spec
  in
  ignore @@ processor @@ fun i -> generate_trace ~config clocks simulations.(i) i
;;

open Simulate

let cmd =
  Cmd.v
    (Cmd.info
       "simulate2"
       ~version
       ~doc:"Simulate a CCSL+ specification using BDD backend.")
  @@ Term.ret
  @@ let+ specification = spec_file_arg
     and+ output_dir = output_dir_arg
     and+ cores = cores_arg
     and+ horizon = horizon_arg
     and+ steps = steps_arg
     and+ traces = traces_arg
     and+ default_upper_bound = default_upper_bound_arg
     and+ rounding_error = rounding_error_arg in
     let _, m = Mrtccslparsing.load_with_string specification Format.err_formatter in
     let horizon = Option.map Number.Rational.of_decimal_string horizon in
     let default_upper_bound =
       Option.map_or
         ~default:(of_int 1000)
         Number.Rational.of_decimal_string
         default_upper_bound
     in
     let rounding_error =
       Option.map_or
         ~default:(of_frac 1 1000)
         Number.Rational.of_decimal_string
         rounding_error
     in
     let config =
       { cores; output_dir; horizon; steps; traces; default_upper_bound; rounding_error }
     in
     verify_config config;
     `Ok (Ok (simulate ~config m))
;;

let main () = Cmd.eval_result cmd
