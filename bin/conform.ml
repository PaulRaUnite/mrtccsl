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
    value
    & opt (some string) None
    & info [ "o"; "output" ] ~doc:"Path to output directory." ~docv:"OUT")
;;

let resolution_arg =
  Arg.(
    value
    & opt (some rational) None
    & info
        [ "r"; "resolution" ]
        ~doc:
          "Histogram resolution written into a modified specification, indicated by \
           $(MODIFIED_HIST)."
        ~docv:"OUT")
;;

let modified_hist_spec_arg =
  Arg.(
    value
    & opt (some string) None
    & info
        [ "modified_hist" ]
        ~doc:
          "Destination for the modified specification that accomodates the derived \
           parameters as histograms."
        ~docv:"MODIFIED_HIST")
;;

let modified_norm_spec_arg =
  Arg.(
    value
    & opt (some string) None
    & info
        [ "modified_norm" ]
        ~doc:
          "Destination for the modified specification that accomodates the derived \
           parameters as normal distributions."
        ~docv:"MODIFIED_NORM")
;;

open Interpretation

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
  VarMap.mapi
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
       Printf.printf
         "%s : mean %s ; std %s\n"
         var
         (Rational.to_string mean)
         (Rational.to_string std);
       mean, std)
    params
;;

let write (module H : Frequency.S) output_dirname params =
  let filename var = Printf.sprintf "%s/%s.freq" output_dirname var in
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

let infinicent_difference = Rational.of_pair (1, 100000)

let convert_trace trace =
  let prev_time = ref Rational.minus_one in
  let fix_time time =
    let new_time =
      if Rational.equal !prev_time time
      then Rational.(time + infinicent_difference)
      else time
    in
    prev_time := time;
    new_time
  in
  Seq.map
    (fun Trace.{ label; time } ->
       Trace.
         { label = label |> Label.to_seq |> Seq.map (fun c -> c, true) |> VarMap.of_seq
         ; time = fix_time time
         })
    trace
;;

open Mrtccsl.CCSL.Language

let replace_with_hist ~resolution rat_stats spec =
  let Specification.{ clock; duration; integer; continuous; discrete } = spec in
  let continuous =
    List.map
      Cstr.(
        fun (v, dist) ->
          if VarMap.mem v rat_stats
          then v, Distribution.Continuous.Histogram { resolution }
          else v, dist)
      continuous
  in
  Specification.{ clock; duration; integer; continuous; discrete }
;;

(* TODO: do the integer params too *)
let correct_spec rat_stats spec =
  let Specification.{ clock; duration; integer; continuous; discrete } = spec in
  let clock, to_shift =
    List.fold_left
      (fun (clock, to_shift) c ->
         let shift_var, c =
           match c with
           | Cstr.AbsPeriodic { out; period; error = Var error; offset } ->
             (match VarMap.find_opt error rat_stats with
              | Some (mean, _) ->
                ( Some error
                , Cstr.AbsPeriodic
                    (* TODO: this is incorrect calibration *)
                    { out; period = Rational.(period + mean); error = Var error; offset }
                )
              | None -> None, Cstr.AbsPeriodic { out; period; error = Var error; offset })
           | Cstr.CumulPeriodic { out; period; error = Var error; offset } ->
             (match VarMap.find_opt error rat_stats with
              | Some (mean, _) ->
                ( Some error
                , Cstr.CumulPeriodic
                    { out; period = Rational.(period + mean); error = Var error; offset }
                )
              | None ->
                None, Cstr.CumulPeriodic { out; period; error = Var error; offset })
           | c -> None, c
         in
         c :: clock, List.cons_opt shift_var to_shift)
      ([], [])
      clock
  in
  ( to_shift
  , Specification.{ clock = List.rev clock; duration; integer; continuous; discrete } )
;;

let modify_hist_mod
      ~replace_with
      rat_stats
      Mrtccsl.CCSL.Language.Module.{ assertions; structure; assumptions }
  =
  let modify_spec spec = correct_spec rat_stats (replace_with rat_stats spec) in
  let assumption_shift, assumptions = List.split_map modify_spec assumptions
  and structure_shift, structure = modify_spec structure
  and assertions_shift, assertions = List.split_map modify_spec assertions in
  let assumption_shift = List.concat assumption_shift
  and assertions_shift = List.concat assertions_shift in
  let vars_to_shift =
    List.concat (assumption_shift :: assertions_shift :: [ structure_shift ])
  in
  vars_to_shift, Mrtccsl.CCSL.Language.Module.{ assumptions; structure; assertions }
;;

let shift_parameters rat_stats rat_params vars_to_shift =
  List.fold_left
    (fun rat_params var ->
       VarMap.update
         var
         (Option.map (fun freqs ->
            let mean, _ = VarMap.find var rat_stats in
            Frequency.ContinuousExact.map (fun x -> Rational.(x - mean)) freqs))
         rat_params)
    rat_params
    vars_to_shift
;;

let output_hist ~modified_hist_spec_path ~output_dir ~rat_stats ~rat_params ~resolution m =
  let resolution = Option.value ~default:(Rational.of_pair (1, 1000000)) resolution in
  let m, rat_params =
    if Option.is_some modified_hist_spec_path
    then (
      let shift_vars, m =
        modify_hist_mod ~replace_with:(replace_with_hist ~resolution) rat_stats m
      in
      m, shift_parameters rat_stats rat_params shift_vars)
    else m, rat_params
  in
  Option.iter
    (fun output_dir ->
       (* write (module Frequency.Discrete) output_dir int_params; *)
       write (module Frequency.ContinuousExact) output_dir rat_params)
    output_dir;
  Option.iter
    (fun filename ->
       Sys.write_file ~filename (fun ch ->
         let fmt = Format.formatter_of_out_channel ch in
         Mrtccsl.CCSL.Language.Module.unparse
           Format.pp_print_string
           Format.pp_print_string
           Format.pp_print_string
           Format.pp_print_string
           Format.pp_print_string
           (fun fmt n -> Format.fprintf fmt "%as" Rational.pp n)
           (fun rate -> Rational.div Rational.one rate)
           fmt
           m))
    modified_hist_spec_path
;;

let replace_with_normal rat_stats spec =
  let Specification.{ clock; duration; integer; continuous; discrete } = spec in
  let continuous =
    List.map
      Cstr.(
        fun (v, dist) ->
          match VarMap.find_opt v rat_stats with
          | Some (mean, deviation) ->
            v, Distribution.Continuous.Normal { mean; deviation }
          | None -> v, dist)
      continuous
  in
  Specification.{ clock; duration; integer; continuous; discrete }
;;

let spec_add_normal_bounds rat_stats to_shift =
  let module S = Set.Make (String) in
  let to_shift = S.of_list to_shift in
  let normal_bounds =
    rat_stats
    |> VarMap.to_seq
    |> Seq.flat_map (fun (var, (mean, std)) ->
      let std2 = Rational.(of_int 2 * std) in
      if S.mem var to_shift
      then (
        let right_bound = Rational.(std2)
        and left_bound = Rational.(-std2) in
        let left_bound =
          if Rational.less left_bound Rational.zero then Rational.zero else left_bound
        in
        List.to_seq
          [ Cstr.NumRelation (var, `LessEq, Const right_bound)
          ; Cstr.NumRelation (var, `MoreEq, Const left_bound)
          ])
      else (
        let left_bound = Rational.(mean - std2)
        and right_bound = Rational.(mean + std2) in
        let left_bound =
          if Rational.less left_bound Rational.zero then Rational.zero else left_bound
        in
        List.to_seq
          [ Cstr.NumRelation (var, `LessEq, Const right_bound)
          ; Cstr.NumRelation (var, `MoreEq, Const left_bound)
          ]))
    |> List.of_seq
  in
  Specification.{ empty with duration = normal_bounds }
;;

let mod_add_normal_bounds rat_stats to_shift m =
  let bound_spec = spec_add_normal_bounds rat_stats to_shift in
  Module.{ m with assumptions = bound_spec :: m.assumptions }
;;

let output_norm ~modified_norm_spec_path ~rat_stats m =
  Option.iter
    (fun filename ->
       let to_shift, m = modify_hist_mod ~replace_with:replace_with_normal rat_stats m in
       let m = mod_add_normal_bounds rat_stats to_shift m in
       Sys.write_file ~filename (fun ch ->
         let fmt = Format.formatter_of_out_channel ch in
         Mrtccsl.CCSL.Language.Module.unparse
           Format.pp_print_string
           Format.pp_print_string
           Format.pp_print_string
           Format.pp_print_string
           Format.pp_print_string
           (fun fmt n -> Format.fprintf fmt "%as" Rational.pp n)
           (fun rate -> Rational.div Rational.one rate)
           fmt
           m))
    modified_norm_spec_path
;;

let check_traces
      ~output_dir
      ~spec_filename
      ~trace_files
      ~modified_hist_spec_path
      ~modified_norm_spec_path
      ~resolution
  =
  let open Mrtccsl.Backend.Machine.Diagram in
  let traces =
    List.map
      (fun file ->
         let _, trace = IO.CSV.read (open_in file) in
         convert_trace trace)
      trace_files
  in
  let _, m = Mrtccslparsing.load_with_string spec_filename Format.err_formatter in
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
  let rat_stats = rat_stats rat_params in
  output_hist ~modified_hist_spec_path ~output_dir ~rat_stats ~rat_params ~resolution m;
  output_norm ~modified_norm_spec_path ~rat_stats m
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
  and+ output_dir = output_dir_arg
  and+ modified_hist_spec_path = modified_hist_spec_arg
  and+ modified_norm_spec_path = modified_norm_spec_arg
  and+ resolution = resolution_arg in
  let traces = if List.length trace_files = 0 then [ "-" ] else trace_files in
  if traces |> List.filter (String.equal "-") |> List.length > 1
  then `Error (false, "can read stdin only once")
  else
    `Ok
      (Ok
         (check_traces
            ~output_dir
            ~spec_filename
            ~trace_files
            ~modified_hist_spec_path
            ~modified_norm_spec_path
            ~resolution))
;;

let main () = Cmd.eval_result cmd
