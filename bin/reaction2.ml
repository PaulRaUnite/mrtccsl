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

module Net =
  CauseEffect.V1.EventEqTransition
    (struct
      module Place = String
      module Transition = String
      module Event = String
      module Color = String
      module Probe = String
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

let extract_probes ~sequalizer ~network_decl trace =
  let trace = Trace.sequalize_trace ~label_to_seq:sequalizer trace in
  let compiled_network = Net.of_decl network_decl in
  let compiled_network = Net.consume_seq_trace compiled_network trace in
  let probes = Net.extracted compiled_network in
  probes
;;

let process_probes ~with_interval ~cause ~conseq probes =
  let open CauseEffect.Token in
  Net.Probes.map
    (fun (m, raw_tokens) ->
       let color_guard = m in
       let relevant_tokens =
         Net.select_relevant_tokens
           ~cause
           ~conseq
           color_guard
           (Dynarray.to_seq raw_tokens)
       in
       let tokens =
         if with_interval
         then Net.full_interval relevant_tokens
         else
           Seq.map
             (fun x ->
                ( Net.Token.
                    { instant = "", Rational.zero
                    ; annotation =
                        Net.Token.Annot.
                          { colors = Net.Token.Coloring.empty
                          ; external_span = Rational.zero, Rational.zero
                          }
                    }
                , x ))
             relevant_tokens
       in
       Seq.map
         (fun (prev_ref, token) ->
            let start = List.hd @@ Net.Token.non_transitive_causes token
            and finish = Net.Token.root_mark token in
            (* should be fully initialized by this point *)
            let open Net.Token in
            let _, time0 = prev_ref.instant
            and _, time1 = start.instant
            and _, time2 = finish.instant in
            let open Rational in
            let interval = time1 - time0
            and reaction = time2 - time1
            and total = time2 - time0 in
            (* print_endline @@ Sexplib.Sexp.to_string_hum @@ Net.Token.sexp_of_t token; *)
            (* if Rational.equal reaction (Rational.of_int 10) then failwith "tehe"; *)
            if with_interval
            then [ "interval", interval / total; "reaction", reaction / total ], total
            else [ "reaction", Rational.one ], reaction)
         tokens)
    probes
;;

let extract_histogram ~scale reactions =
  let round_to = Rational.round_floor scale in
  let histogram = Stats.weighted_histogram scale round_to reactions in
  histogram
;;

let sum_probe_reactions p1 p2 =
  Net.Probes.union (fun _ r1 r2 -> Some (Seq.append r1 r2)) p1 p2
;;

let do_command
      ~scale
      ~output_dir
      ~microstep_file
      ~network_file
      ~with_interval
      ~cause
      ~conseq
      trace_files
  =
  let traces = List.map load_trace trace_files in
  let network_decl = load_declaration network_file in
  let sequalizer = microstep_sequalizer microstep_file in
  let do_trace trace =
    let probes = extract_probes ~sequalizer ~network_decl trace in
    let reaction_probes = process_probes ~with_interval ~cause ~conseq probes in
    reaction_probes
  in
  let all_probes = List.map do_trace traces in
  let probes = List.fold_left sum_probe_reactions Net.Probes.empty all_probes in
  Net.Probes.iter
    (fun chain_id overall_reactions ->
       let hist = extract_histogram ~scale overall_reactions in
       let filename = plain_weighted_histogram_name output_dir chain_id in
       write_histogram filename hist)
    probes
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
    | "early" -> Ok CauseEffect.Declaration.Early
    | "late" -> Ok CauseEffect.Declaration.Late
    | s -> Error (`Msg (Printf.sprintf "wrong end semantics: %s" s))
  and pp ppf x =
    Format.fprintf
      ppf
      "%s"
      (match x with
       | CauseEffect.Declaration.Early -> "early"
       | CauseEffect.Declaration.Late -> "late")
  in
  Arg.conv (parser, pp)
;;

let start_semantics_arg =
  Arg.(
    value
    & opt end_semantics CauseEffect.Declaration.Early
    & info
        [ "start" ]
        ~doc:"Selection of chain cause instants from equivalent."
        ~docv:"START_SEM")
;;

let finish_semantics_arg =
  Arg.(
    value
    & opt end_semantics CauseEffect.Declaration.Early
    & info
        [ "finish" ]
        ~doc:"Selection of chain consequnce instants from equivalent."
        ~docv:"FINISH_SEM")
;;

let interval_flag =
  Arg.(
    value
    & flag
    & info [ "i"; "interval" ] ~doc:"Records interval duration between successful chains.")
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
  and+ output_dir = output_dir_arg
  and+ with_interval = interval_flag in
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
            ~with_interval
            ~cause
            ~conseq
            traces))
;;

let main () = Cmd.eval_result cmd
