open Common
open Prelude
open Aux
open Cmdliner
open Cmdliner.Term.Syntax
open Number

module Label = struct
  include Set.Make (String)
  module E = String
end

module IO = Common.Trace.MakeIO (Rational) (Label)

let trace_arg =
  Arg.(
    value
    & pos_right 0 non_dir_file []
    & info
        []
        ~doc:"The traces to extract parameter from."
        ~docv:"TRACE"
        ~absent:"Uses stdin")
;;

let spec_file_arg =
  Arg.(
    required
    (* TODO: make it possible to use stdin (need modifications to parsing and its error reporting) *)
    & pos 0 (some non_dir_file) None
    & info [] ~doc:"Path to specification file. Used to " ~docv:"SPEC")
;;

let output_dir_arg =
  Arg.(
    required
    & opt (some string) None
    & info [ "o"; "output" ] ~doc:"Path to output directory." ~docv:"OUT")
;;

open Interpretation

let convert_trace trace =
  Seq.map
    (fun Trace.{ label; time } ->
       Trace.
         { label = label |> Label.to_seq |> Seq.map (fun c -> c, true) |> VarMap.of_seq
         ; time
         })
    trace
;;

let insert_sample (module H : Frequency.S) acc (samples : H.bin Diagram.sample VarMap.t) =
  VarMap.merge
    (fun _ hist sample ->
       match hist, sample with
       | Some hist, Some (Diagram.Sample sample) -> Some (H.add sample 1 hist)
       | Some hist, None -> Some hist
       | None, Some (Diagram.Sample sample) -> Some (H.add sample 1 H.empty)
       | None, None -> None)
    acc
    samples
;;

let merge_samples (module H : Frequency.S) acc1 acc2 =
  VarMap.union (fun _ h1 h2 -> Some (H.sum h1 h2)) acc1 acc2
;;

let mean sum n = Mpfrf.div_ui sum n Mpfr.Near

let int_stats params =
  VarMap.iter
    (fun var hist ->
       let mean =
         Frequency.mean (module Frequency.Discrete) (module Frequency.Discrete.STDN) hist
       in
       let std =
         Frequency.std
           (module Frequency.Discrete)
           (module Frequency.Discrete.STDN)
           ~mean
           hist
       in
       Printf.printf "%s : mean %f ; std %f\n" var mean std)
    params
;;

let rat_stats params =
  VarMap.iter
    (fun var hist ->
       let mean =
         Frequency.mean
           (module Frequency.ContinuousExact)
           (module Frequency.ContinuousExact.STDN)
           hist
       in
       let std =
         Frequency.std
           (module Frequency.ContinuousExact)
           (module Frequency.ContinuousExact.STDN)
           ~mean
           hist
       in
       Printf.printf "%s : mean %f ; std %f\n" var mean std)
    params
;;

let write (module H : Frequency.S) output_dirname params =
  let filename var = Printf.sprintf "%s/%s" output_dirname var in
  VarMap.iter
    (fun var hist ->
       let filename = filename var in
       Sys.write_file ~filename (fun file -> Frequency.write (module H) file hist))
    params
;;

let derive_parameters ~acceptor trace
  : Frequency.Discrete.t VarMap.t * Frequency.ContinuousExact.t VarMap.t
  =
  let open Mrtccsl.Backend.Machine.Diagram in
  let check_seq = ParallelAcceptance.accept_trace acceptor trace in
  let r =
    Seq.fold_leftr
      (fun (intacc, ratacc) r ->
         let open Result.Syntax in
         let* _, (intparams, ratparams) = r in
         Ok
           ( insert_sample (module Frequency.Discrete) intacc intparams
           , insert_sample (module Frequency.ContinuousExact) ratacc ratparams ))
      (Ok (VarMap.empty, VarMap.empty))
      check_seq
  in
  (* TODO: add explanation and some debugging info *)
  Result.get_ok r
;;

let check_traces ~spec_filename ~trace_files ~output_dir =
  let open Mrtccsl.Backend.Machine.Diagram in
  let traces =
    List.map
      (fun file ->
         let _, trace = IO.CSV.read (open_in file) in
         convert_trace trace)
      trace_files
  in
  let _, m = Mrtccslparsing.load_with_string spec_filename Format.err_formatter in
  (* TODO: maybe reconsider flattening *)
  let spec = Mrtccsl.CCSL.Language.Module.flatten m in
  let acceptor = ParallelAcceptance.of_spec spec in
  let params = List.map (derive_parameters ~acceptor) traces in
  let int_params, rat_params =
    List.fold_left
      (fun (inttotal, rattotal) (intparams, ratparams) ->
         ( merge_samples (module Frequency.Discrete) inttotal intparams
         , merge_samples (module Frequency.ContinuousExact) rattotal ratparams ))
      (VarMap.empty, VarMap.empty)
      params
  in
  int_stats int_params;
  rat_stats rat_params;
  write (module Frequency.Discrete) output_dir int_params;
  write (module Frequency.ContinuousExact) output_dir rat_params
;;

let cmd =
  let man =
    [ `S Manpage.s_description
    ; `P "$(cmd) checks constraint satisfaction and extracts constraint parameters"
    ]
  in
  Cmd.v
    (Cmd.info
       "conform"
       ~version
       ~doc:"Check constraint satisfaction and extract constraint parameters"
       ~man)
  @@ Term.ret
  @@
  let+ spec_filename = spec_file_arg
  and+ trace_files = trace_arg
  and+ output_dir = output_dir_arg in
  let traces = if List.length trace_files = 0 then [ "-" ] else trace_files in
  if traces |> List.filter (String.equal "-") |> List.length > 1
  then `Error (false, "can read stdin only once")
  else `Ok (Ok (check_traces ~spec_filename ~trace_files ~output_dir))
;;

let main () = Cmd.eval_result cmd
