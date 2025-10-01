open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
module Stats = Stats.Make (String) (Number.Rational)
open FnCh
open Common

let extract_reaction
      ~semantics
      trace_streams
      reactions_dir
      histogram_param
      chains
      output_dir
  =
  let session = S.Session.create () in
  let to_inner = S.Session.to_offset session in
  let to_outer = S.Session.of_offset session in
  let channel_to_trace ch = FnCh.Export.read_csv session ch |> Dynarray.of_iter in
  let traces = List.map channel_to_trace trace_streams in
  let process_chain (chain_name, chain) =
    let chain = Chain.map to_inner chain in
    let categories = Chain.sampling_clocks chain
    and interest = Chain.spans_of_interest chain in
    let trace_to_chain_instances trace =
      let trace = Dynarray.to_iter trace in
      let chains, _ = trace_to_chain semantics chain trace in
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
              let filename = reaction_name dir chain_name (Tuple.map2 to_outer span) in
              (Sys.write_file ~filename)
                (FnCh.reaction_times_to_csv session categories interest chain_instances))
           interest)
      reactions_dir;
    let print_histogram scale =
      List.iter
        (fun span ->
           let tagged_reaction_times =
             FnCh.categorized_reaction_times session categories span chain_instances
           in
           let stats =
             Stats.histogram (Number.Rational.round_floor scale) tagged_reaction_times
           in
           let filename =
             histogram_name output_dir chain_name (Tuple.map2 to_outer span)
           in
           Sys.write_file ~filename (Format.formatter_of_out_channel >> Stats.to_csv stats))
        interest
    in
    Option.iter print_histogram histogram_param
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
    & opt (some dir) None
    & info
        [ "l"; "list" ]
        ~doc:
          "Directory where CSV lists of reaction times categorized by misses will be \
           placed."
        ~docv:"LIST")
;;

let histogram_arg =
  Arg.(
    value
    & opt (some rational) None
    & info
        [ "h"; "hist" ]
        ~doc:
          "Scale with which CSV histograms of reaction times are calculated, categorized \
           by misses and collected using scale."
        ~docv:"HIST")
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
  and+ histogram = histogram_arg
  and+ chain = chain_arg
  and+ output = output_dir_arg
  and+ semantics = chain_semantics_arg in
  let traces = if List.length traces = 0 then [ "-" ] else traces in
  if chain :: traces |> List.filter (String.equal "-") |> List.length > 1
  then `Error (false, "can read stdin only once")
  else (
    let open_in_chan = function
      | "-" -> stdin
      | file -> open_in file
    in
    let trace_inputs = List.map open_in_chan traces
    and chain_input = open_in_chan chain in
    let chains = Chain.parse_from_channel chain_input in
    `Ok
      (Ok (extract_reaction ~semantics trace_inputs reaction_list histogram chains output)))
;;

let main () = Cmd.eval_result cmd
