open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
open FnCh

let process input output chain =
  let lines = In_channel.with_open_text input In_channel.input_all in
  let lines = String.split_on_char '\n' lines in
  let session = S.Session.create () in
  let to_inner = S.Session.to_offset session in
  let trace =
    List.filter_map
      (fun line ->
         let parse line =
           Scanf.sscanf line " %s %f" (fun s t ->
             A.L.singleton (S.Session.save session s), Number.Rational.of_float t)
         in
         try Some (parse line) with
         | End_of_file -> None)
      lines
  in
  let _ = Format.printf "chain computation for %s\n" input in
  let chain = Chain.map to_inner chain in
  let trace = Iter.of_list trace in
  let chains, _ = trace_to_chain Randomized chain trace in
  List.iter
    (fun point ->
       FnCh.print_statistics session point Format.std_formatter (Iter.of_dynarray chains))
    (Chain.sampling_clocks chain);
  let _ = Format.print_string "reaction computation\n" in
  let interest = Chain.spans_of_interest chain in
  let data_file = open_out output in
  let _ =
    FnCh.reaction_times_to_csv
      session
      (Chain.sampling_clocks chain)
      interest
      data_file
      (Iter.of_dynarray chains)
  in
  close_out data_file
;;

let () =
  let input = ref "" in
  let output = ref "" in
  let chain = ref "" in
  let usage_msg = "reaction <input> -o <output> -c <chain>" in
  let _ =
    Arg.parse
      [ "-o", Arg.Set_string output, "output file"
      ; "-c", Arg.Set_string chain, "chain spec"
      ]
      (fun dir -> input := dir)
      usage_msg
  in
  if !input = "" then invalid_arg "empty input";
  if !output = "" then invalid_arg "empty output";
  if !chain = "" then invalid_arg "empty chain";
  process !input !output (Chain.parse !chain)
;;
