open Common
open Prelude
open Mrtccsl
open Number
module Clock = String

module L = struct
  module E = Clock
  include Set.Make (Clock)
end

module IO = Common.Trace.MakeIO (Rational) (L)

module React =
  CauseEffect.Reaction.Make
    (CauseEffect.Extraction.V1.EventEqTransition)
    (struct
      module Place = String
      module Event = String
      module Chain = String
    end)
    (Rational)

module Stats = Stats.Make (String) (Rational)
open Aux

let open_in_chan = function
  | "-" -> stdin
  | file -> open_in file
;;

let write_histogram filename hist =
  Sys.write_file ~filename (Format.formatter_of_out_channel >> Stats.to_csv hist)
;;

let load_declaration network_filename =
  let contents = read_to_string network_filename in
  let sexp = Sexplib.Sexp.of_string contents in
  let decl =
    CauseEffect.Declaration.t_of_sexp
      String.t_of_sexp
      String.t_of_sexp
      String.t_of_sexp
      sexp
  in
  decl
;;

let load_trace filename =
  let ch = open_in_chan filename in
  snd (IO.CSV.read ch)
;;

let microstep_sequalizer microstep_spec_filename =
  let open CCSL.MicroStep in
  let contents = read_to_string microstep_spec_filename in
  let spec =
    HardRelation.spec_of_sexp Clock.t_of_sexp @@ Sexplib.Sexp.of_string contents
  in
  let compiled_spec = HardRelation.compile spec in
  let sequalizer label =
    let iter = L.to_iter label in
    let randomized = HardRelation.arrange_randomly compiled_spec iter in
    List.to_seq randomized
  in
  sequalizer
;;

let extract_histogram ~scale reactions =
  let round_to = Rational.round_floor scale in
  let histogram = Stats.weighted_histogram scale round_to reactions in
  histogram
;;

let do_command ~scale ~output_dir ~microstep_file ~network_file ~cause ~conseq trace_files
  =
  let traces = List.map load_trace trace_files in
  let network_decl = load_declaration network_file in
  let sequalizer = microstep_sequalizer microstep_file in
  let do_trace trace =
    let trace = Trace.sequalize_trace ~label_to_seq:sequalizer trace in
    let result = React.collect ~cause ~conseq network_decl trace in
    result
  in
  let all_results = List.map do_trace traces in
  let results =
    List.fold_left
      (React.ChainMap.merge (fun _ acc x ->
         let acc = Option.value ~default:[] acc in
         match x with
         | Some x -> Some (x :: acc)
         | None -> Some acc))
      React.ChainMap.empty
      all_results
  in
  React.ChainMap.iter
    (fun probe_id reactions ->
       let without = React.seq_list_without reactions
       and full = React.seq_list_full reactions
       and reduced = React.seq_list_reduced reactions in
       let histogram_data = [ "without", without; "full", full; "reduced", reduced ] in
       List.iter
         (fun (name, data) ->
            let hist = extract_histogram ~scale data in
            let filename = plain_histogram_name output_dir probe_id name in
            write_histogram filename hist)
         histogram_data)
    results
;;

open Cmdliner
open Cmdliner.Term.Syntax

let trace_arg =
  Arg.(
    value
    & pos_right 1 non_dir_file []
    & info
        []
        ~doc:"The trace to extract reaction time from."
        ~docv:"TRACE"
        ~absent:"Uses stdin")
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

let effect_network_specification_arg =
  Arg.(
    required
    & pos 0 (some non_dir_file) None
    & info
        []
        ~doc:"Path to cause-effect network specification file."
        ~docv:"CAUSAL_NETWORK")
;;

let microstep_order_specification_arg =
  Arg.(
    required
    & pos 1 (some non_dir_file) None
    & info [] ~doc:"Path to microstep order specification file." ~docv:"MICROSTEP")
;;

let end_semantics =
  let parser = function
    | "early" -> Ok CauseEffect.Reaction.Early
    | "late" -> Ok CauseEffect.Reaction.Late
    | s -> Error (`Msg (Printf.sprintf "wrong end semantics: %s" s))
  and pp ppf x =
    Format.fprintf
      ppf
      "%s"
      (match x with
       | CauseEffect.Reaction.Early -> "early"
       | CauseEffect.Reaction.Late -> "late")
  in
  Arg.conv (parser, pp)
;;

let start_semantics_arg =
  Arg.(
    value
    & opt end_semantics CauseEffect.Reaction.Early
    & info
        [ "start" ]
        ~doc:"Selection of chain cause instants from equivalent."
        ~docv:"START_SEM")
;;

let finish_semantics_arg =
  Arg.(
    value
    & opt end_semantics CauseEffect.Reaction.Early
    & info
        [ "finish" ]
        ~doc:"Selection of chain consequnce instants from equivalent."
        ~docv:"FINISH_SEM")
;;

let cmd =
  let man = [ `S Manpage.s_description; `P "$(cmd) computes reaction time" ] in
  Cmd.v
    (Cmd.info
       "reaction2"
       ~version
       ~doc:"Compute reaction times of traces using functional chain specification"
       ~man)
  @@ Term.ret
  @@
  let+ network_file = effect_network_specification_arg
  and+ microstep_file = microstep_order_specification_arg
  and+ traces = trace_arg
  and+ scale = scale_arg
  and+ cause = start_semantics_arg
  and+ conseq = finish_semantics_arg
  and+ output_dir = output_dir_arg in
  let traces = if List.length traces = 0 then [ "-" ] else traces in
  if
    network_file :: microstep_file :: traces
    |> List.filter (String.equal "-")
    |> List.length
    > 1
  then `Error (false, "can read stdin only once")
  else
    `Ok
      (Ok
         (do_command
            ~scale
            ~output_dir
            ~microstep_file
            ~network_file
            ~cause
            ~conseq
            traces))
;;

let main () = Cmd.eval_result cmd
