open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
open FnCh

let func_chain_spec =
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

let process filename =
  let lines =
    In_channel.with_open_text (Printf.sprintf "./traces/%s" filename) In_channel.input_all
  in
  let lines = String.split_on_char '\n' lines in
  let trace =
    List.filter_map
      (fun line ->
         let parse line =
           Scanf.sscanf line " %s %f" (fun s t ->
             A.L.singleton s, Number.Rational.of_float t)
         in
         try Some (parse line) with
         | End_of_file -> None)
      lines
  in
  (* let _ = List.print (print_endline << A.solution_to_string) trace in *)
  let _ = Printf.printf "chain computation for %s\n" filename in
  let trace = Array.to_seq (Array.of_list trace) in
  let chains, _ = trace_to_chain Randomized func_chain_spec trace in
  let _ = FnCh.print_statistics "a.s" (List.to_seq chains) in
  let _ = print_endline "reaction computation" in
  let interest = points_of_interest func_chain_spec in
  let reactions = FnCh.reaction_times interest (List.to_seq chains) in
  let name = Filename.remove_extension filename in
  let data_file = open_out (Printf.sprintf "./plots/data/%s_reaction_times.csv" name) in
  let _ =
    Printf.fprintf
      data_file
      "%s"
      (FnCh.reaction_times_to_csv [ "a.s" ] interest reactions)
  in
  close_out data_file
;;

let () =
  let traces = Sys.readdir "./traces/" in
  Array.iter process traces
;;
