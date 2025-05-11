open Mrtccsl
open Prelude
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
open Number.Rational
open FnCh

let func_chain_spec =
  FnCh.
    { first = "s.s"
    ; rest =
        [ `Causality, "s.f"
        ; `Causality, "c.s"
        ; `Causality, "c.f"
        ; `Sampling, "a.s"
        ; `Causality, "a.f"
        ]
    }
;;

let process name =
  let lines =
    In_channel.with_open_text (Printf.sprintf "%s.txt" name) In_channel.input_all
  in
  let lines = String.split_on_char '\n' lines in
  let trace =
    List.filter_map
      (fun line ->
         let parse line =
           Scanf.sscanf line " %s %f" (fun s t -> A.L.singleton s, Rational.of_float t)
         in
         try Some (parse line) with
         | End_of_file -> None)
      lines
  in
  (* let _ = List.print (print_endline << A.solution_to_string) trace in *)
  let _ = print_endline "chain computation" in
  let trace = Array.to_seq (Array.of_list trace) in
  let chains, _ = trace_to_chain Earliest func_chain_spec trace in
  let start, finish = FnCh.chain_start_finish_clocks func_chain_spec in
  let _ = print_endline "reaction computation" in
  let reactions = FnCh.reaction_times start finish (List.to_seq chains) in
  let data_file = open_out (Printf.sprintf "./plots/data/%s_reaction_times.csv" name) in
  let _ =
    Printf.fprintf data_file "%s" (FnCh.reaction_times_to_csv [ "a.s" ] reactions)
  in
  close_out data_file
;;

let () =
  let names =
    [ "simpy_uniform_nores"; "simpy_normal_nores"; "simpy_uniform_1res"; "simpy_normal_1res" ]
  in
  List.iter process names
;;
