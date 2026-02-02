open Prelude
open Common
open Cmdliner
open Cmdliner.Term.Syntax

let spec_file_arg =
  Arg.(
    required
    (* TODO: make it possible to use stdin (need modifications to parsing and its error reporting) *)
    & pos 0 (some non_dir_file) None
    & info [] ~doc:"Path to specification file." ~docv:"SPEC")
;;

let trace_arg =
  Arg.(
    required
    & pos 1 (some inline_in_channel) None
    & info [] ~doc:"Deadlocked trace. Skip or use - to indicate stdin." ~docv:"TRACE")
;;

let nextclock_arg =
  Arg.(
    required
    & pos 2 (some string) None
    & info [] ~doc:"Clock to check which constraint has problem with")
;;

open Mrtccsl
module A = Backend.Naive.Make (String) (Number.Rational)
module ST = Backend.Naive.Strategy (A)
module Opt = Optimization.Order.Make (String)
module IO = Backend.Trace.MakeIO (Number.Rational) (A.L)

let debug_trace spec_filename trace clock =
  let _, m = Mrtccslparsing.load_with_string spec_filename Format.err_formatter in
  (*TODO: remove flattening*)
  let spec = Mrtccsl.Language.Module.flatten m in
  let spec = Opt.optimize spec in
  let clocks, trace = IO.CSV.read trace in
  let trace = Iter.map IO.step_to_pair trace in
  if not (List.mem clock clocks)
  then print_endline "clock is not found in trace, check spelling"
  else (
    let a = A.of_spec spec in
    let result = A.accept_trace a Number.Rational.minusone trace in
    Option.iter
      (fun last_time ->
         let solutions = A.try_force_clock a last_time clock in
         Iter.iter
           (fun (l, _) -> if A.L.is_empty l then (print_endline "is empty:" ; print_endline @@ A.L.to_string l))
           solutions;
         print_endline @@ A.guard_to_string solutions)
      result)
;;

let cmd : (unit, string) result Cmd.t =
  Cmd.v (Cmd.info "debug" ~doc:"Debug a specification using trace as prefix.")
  @@ Term.ret
  @@ let+ spec_filename = spec_file_arg
     and+ trace = trace_arg
     and+ clock = nextclock_arg in
     let trace = Common.get_in_channel trace in
     `Ok (Ok (debug_trace spec_filename trace clock))
;;
