open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module IO = Mrtccsl.Automata.Trace.MakeIO (Number.Rational) (FnCh.A.L)
module A = FnCh.A
module Stats = Stats.Make (String) (Number.Rational)
open FnCh
open Common

let open_in_chan = function
  | "-" -> stdin
  | file -> open_in file
;;

let extract_reaction
      ~semantics
      trace_streams
      reactions_dir
      chistogram_param
      whistogram_param
      scale
      chains
      output_dir
  =
  let channel_to_trace filename =
    let ch = open_in_chan filename in
    (* print_endline filename; *)
    snd (IO.CSV.read ch) |> Iter.map IO.step_to_pair |> Dynarray.of_iter
  in
  let traces = List.map channel_to_trace trace_streams in
  let process_chain (chain_name, chain) =
    let categories = Chain.sampling_clocks chain
    and interest = Chain.spans_of_interest chain in
    let trace_to_chain_instances trace =
      let trace = Dynarray.to_iter trace in
      let chains, _ = extract_chains semantics chain trace in
      chains
    in
    let chain_instances =
      traces
      |> Iter.of_list
      |> Iter.map (trace_to_chain_instances >> Dynarray.to_iter)
      |> Iter.concat
    in
    Option.iter
      (fun dir ->
         List.iter
           (fun span ->
              let filename = reaction_name dir chain_name span in
              print_endline filename;
              (Sys.write_file ~filename)
                (FnCh.reaction_times_to_csv categories interest chain_instances))
           interest)
      reactions_dir;
    if chistogram_param
    then
      List.iter
        (fun span ->
           let tagged_reaction_times =
             FnCh.categorized_reaction_times categories span chain_instances
           in
           let stats =
             Stats.category_histogram
               (Number.Rational.round_floor scale)
               tagged_reaction_times
           in
           let filename = categorized_histogram_name output_dir chain_name span in
           Sys.write_file ~filename (Format.formatter_of_out_channel >> Stats.to_csv stats))
        interest;
    let print_weighted_histogram mode =
      let span = Chain.start_finish_clocks chain in
      let discretize_range right_bound =
        let open Number.Rational in
        let whole_parts = to_int (right_bound / scale) in
        Iter.int_range ~start:0 ~stop:whole_parts
        |> Iter.map (fun sample_point -> of_int sample_point * scale)
      in
      let discretize_range =
        match mode with
        | `All -> Some discretize_range
        | `Worst -> None
      in
      let tagged_reaction_times =
        FnCh.weighted_full_reaction_times ?discretize_range chain chain_instances
      in
      let stats =
        Stats.weighted_histogram (Number.Rational.round_floor scale) tagged_reaction_times
      in
      let filename = weighted_histogram_name output_dir chain_name span in
      Sys.write_file ~filename (Format.formatter_of_out_channel >> Stats.to_csv stats)
    in
    Option.iter print_weighted_histogram whistogram_param
  in
  Seq.iter process_chain chains
;;

open Cmdliner
open Cmdliner.Term.Syntax

let trace_arg =
  Arg.(
    value
    & pos_right 0 non_dir_file []
    & info
        []
        ~doc:"The trace to extract reaction time from."
        ~docv:"TRACE"
        ~absent:"Uses stdin")
;;

let reactions_list_arg =
  Arg.(
    value
    & opt (some string) None
    & info
        [ "l"; "list" ]
        ~doc:
          "Directory where CSV lists of reaction times categorized by misses will be \
           placed."
        ~docv:"LIST")
;;

let categorized_histogram_arg =
  Arg.(
    value
    & flag
    & info
        [ "c"; "categorized" ]
        ~doc:"Instruct to categorize by misses and collected using $(i,SCALE)."
        ~docv:"CATEGORIZED_HIST")
;;

let weighted_histogram_arg =
  Arg.(
    value
    & opt (some @@ enum [ "worst", `Worst; "all", `All ]) None
    & info
        [ "w"; "weighted" ]
        ~doc:
          "Instruct to categorize by contributions of individual reactions. When all is \
           specified, $(i,SCALE) variable should be present."
        ~docv:"WEIGHTED_HIST")
;;

let scale_arg =
  Arg.(
    required
    & opt (some rational) None
    & info [ "d"; "scale" ] ~doc:"Scale used for histograms." ~docv:"SCALE")
;;

let output_dir_arg =
  Arg.(
    required
    & opt (some string) None
    & info [ "o"; "output" ] ~doc:"Path to output directory." ~docv:"OUT")
;;

let chain_arg =
  Arg.(
    required
    & pos 0 (some non_dir_file) None
    & info [] ~doc:"Path to chain specification file." ~docv:"CHAIN")
;;

let chain_semantics =
  let parser = function
    | "earliest" -> Ok Earliest
    | "random" -> Ok Randomized
    | "latest" -> Ok Latest
    | "all" -> Ok All
    | s -> Error (`Msg (Printf.sprintf "wrong chain semantics: %s" s))
  and pp ppf x =
    Format.fprintf
      ppf
      "%s"
      (match x with
       | Earliest -> "earliest"
       | Randomized -> "random"
       | Latest -> "latest"
       | All -> "all")
  in
  Arg.conv (parser, pp)
;;

let chain_semantics_arg =
  Arg.(
    value
    & opt chain_semantics Earliest
    & info
        [ "s"; "semantics" ]
        ~doc:"Semantics of the functional chain. Can be earliest, latest, all or random."
        ~docv:"SEMANTICS")
;;

let cmd =
  let man = [ `S Manpage.s_description; `P "$(cmd) computes reaction time" ] in
  Cmd.v
    (Cmd.info
       "reaction"
       ~version
       ~doc:"Compute reaction times of traces using functional chain specification"
       ~man)
  @@ Term.ret
  @@
  let+ traces = trace_arg
  and+ reaction_list = reactions_list_arg
  and+ chistogram = categorized_histogram_arg
  and+ whistogram = weighted_histogram_arg
  and+ scale = scale_arg
  and+ chain = chain_arg
  and+ output = output_dir_arg
  and+ semantics = chain_semantics_arg in
  let traces = if List.length traces = 0 then [ "-" ] else traces in
  if chain :: traces |> List.filter (String.equal "-") |> List.length > 1
  then `Error (false, "can read stdin only once")
  else (
    let chain_input = open_in_chan chain in
    let chains = Chain.parse_from_channel chain_input in
    `Ok
      (Ok
         (extract_reaction
            ~semantics
            traces
            reaction_list
            chistogram
            whistogram
            scale
            chains
            output)))
;;

let main () = Cmd.eval_result cmd
