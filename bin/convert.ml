open Prelude
open Mrtccsl
open Cmdliner
open Cmdliner.Term.Syntax
open Number
open Common
module FnCh = Mrtccsl.Functional_chain.Make (String) (Rational)

let input_arg =
  Arg.(
    value
    & pos 0 (some inline_in_channel) None
    & info [] ~doc:"Trace to be converted. Skip or use - to indicate stdin." ~docv:"TRACE")
;;

let output_arg =
  Arg.(
    value
    & opt (some inline_out_channel) None
    & info
        [ "o"; "output" ]
        ~doc:"Output file. Skip or use - to indicate stdout."
        ~docv:"OUTPUT")
;;

module Native = struct
  module CADP = struct
    let convert input output =
      let session = FnCh.S.Session.create () in
      let trace = FnCh.Export.read_csv session input in
      FnCh.Export.trace_to_cadp session (Format.formatter_of_out_channel output) trace
    ;;

    let cmd =
      Cmd.(
        v
          (info
             "cadp"
             ~doc:"Convert native trace into CADP trace (comma-separated list of events).")
        @@ Term.ret
        @@ let+ input = input_arg
           and+ output = output_arg in
           let input = Option.map_or ~default:stdin get_in_channel input
           and output = Option.map_or ~default:stdout get_out_channel output in
           `Ok (Ok (convert input output)))
    ;;
  end

  module TCADP = struct (*TODO merge timed and untimed*)
    let scale_arg =
      Arg.(
        value
        & opt rational (Rational.of_frac 1 1000)
        & info [ "d"; "delta" ] ~doc:"Discretization delta (scale)." ~docv:"SCALE")
    ;;

    let spec_arg =
      Arg.(
        required
        & opt (some non_dir_file) None
        & info
            [ "s"; "spec" ]
            ~doc:
              "File with specification used to generate the trace. Used to derive \
               microstep ordering."
            ~docv:"SPEC")
    ;;

    type rounding =
      | Near
      | Floor
      | Ceil

    let of_rounding = function
      | Near -> Rational.modulo_near
      | Floor -> Rational.modulo_floor
      | Ceil -> Rational.modulo_ceil
    ;;

    let rounding_to_string = function
      | Near -> "near"
      | Floor -> "floor"
      | Ceil -> "ceil"
    ;;

    let rounding =
      let parser = function
        | "near" -> Ok Near
        | "floor" -> Ok Floor
        | "ceil" -> Ok Ceil
        | s -> Error (`Msg (Printf.sprintf "parsing rounding, unexpected string: %s" s))
      and pp ppf x = Format.fprintf ppf "%s" (rounding_to_string x) in
      Arg.conv (parser, pp)
    ;;

    let mode_arg =
      Arg.(
        value
        & opt rounding Near
        & info
            [ "r"; "round" ]
            ~doc:"Rounding used in discretization. $(docv) is either near, floor or ceil."
            ~docv:"ROUNDING")
    ;;

    let convert ~scale ~m ~rounding_mode input output =
      let spec = Mrtccsl.Ccsl.Language.Module.flatten m in
      let order_hints =
        Ccsl.MicroStep.derive_order Mrtccsl.Ccsl.Language.Specification.(spec.logical)
      in
      let session = FnCh.S.Session.create () in
      let trace = FnCh.Export.read_csv session input in
      FnCh.Export.trace_to_timed_cadp
        session
        (of_rounding rounding_mode ~divisor:scale)
        order_hints
        (Format.formatter_of_out_channel output)
        trace
    ;;

    let cmd =
      Cmd.(
        v
          (info
             "tcadp"
             ~doc:
               "Convert native trace into timed CADP trace (comma-separated list of \
                events with discretized time deltas).")
        @@ Term.ret
        @@ let+ scale = scale_arg
           and+ input = input_arg
           and+ output = output_arg
           and+ spec_file = spec_arg
           and+ rounding_mode = mode_arg in
           let input = Option.map_or ~default:stdin get_in_channel input
           and output = Option.map_or ~default:stdout get_out_channel output in
           Ocolor_format.prettify_formatter Format.std_formatter;
           let ast =
             Mrtccslparsing.Parse.from_file spec_file
             |> Result.map_error (fun pp_e ->
               fun fmt -> Format.fprintf fmt "Parsing error: %a" pp_e)
             |> Result.unwrap ~msg:"Failed in parsing."
           in
           let context, m, errors = Mrtccslparsing.Compile.into_module ast in
           let v2s =
             Mrtccslparsing.Compile.(
               function
               | Explicit v -> List.to_string ~sep:"." Fun.id v
               | Anonymous i -> Printf.sprintf "anon(%i)" i)
           in
           let m = Mrtccsl.Ccsl.Language.Module.map v2s v2s Fun.id v2s v2s Fun.id m in
           if not (List.is_empty errors)
           then (
             Mrtccslparsing.Compile.Context.pp Format.std_formatter context;
             List.iter
               (Mrtccslparsing.Compile.print_compile_error Format.std_formatter)
               errors;
             failwith "Compilation error.")
           else `Ok (Ok (convert ~scale ~m ~rounding_mode input output)))
    ;;
  end

  module SvgBob = struct
    let print_svgbob ~tasks ~vertical input output =
      let session = FnCh.S.Session.create () in
      let trace = FnCh.Export.read_csv session input in
      let trace = Iter.persistent trace in
      let clocks = FnCh.S.Session.identifiers session in
      let tasks = List.map (Trace.map_task (FnCh.S.Session.to_offset session)) tasks in
      let bob =
        if vertical
        then FnCh.Export.trace_to_vertical_svgbob
        else FnCh.Export.trace_to_svgbob ?precision:None
      in
      let formatter = Format.formatter_of_out_channel output in
      bob ~numbers:false ~tasks session clocks formatter trace;
      Format.pp_print_flush formatter ()
    ;;

    let vertical_flag =
      Arg.(
        value
        & flag
        & info [ "v"; "vertical" ] ~doc:"Print chronogram vertically (allows streaming).")
    ;;

    let tasks_arg =
      Arg.(
        value
        & opt (some non_dir_file) None
        & info [ "t"; "tasks" ] ~doc:"Tasks specification (CSV file).")
    ;;

    let load_tasks file =
      let rows = Csv.Rows.load ~has_header:true file in
      List.map
        Mrtccsl.Trace.(
          fun row ->
            let name = Csv.Row.find row "name"
            and release = Csv.Row.find row "release"
            and start = Csv.Row.find row "start"
            and finish = Csv.Row.find row "finish"
            and deadline = Csv.Row.find row "deadline" in
            { name; start; finish; release; deadline })
        rows
    ;;

    let cmd =
      Cmd.v (Cmd.info "svgbob" ~doc:"Print svgbob chronogram of the trace.")
      @@ Term.ret
      @@ let+ input = input_arg
         and+ output = output_arg
         and+ vertical = vertical_flag
         and+ tasks_file = tasks_arg in
         let input = Option.map_or ~default:stdin get_in_channel input
         and output = Option.map_or ~default:stdout get_out_channel output
         and tasks = Option.value ~default:[] @@ Option.map load_tasks tasks_file in
         `Ok (Ok (print_svgbob ~vertical ~tasks input output))
    ;;
  end

  let cmd =
    let default = Term.(ret (const (`Help (`Pager, Some "native")))) in
    Cmd.group
      ~default
      (Cmd.info
         "native"
         ~version
         ~doc:"Convert native (precise) trace into other formats.")
      [ CADP.cmd; TCADP.cmd; SvgBob.cmd ]
  ;;
end

let cmd : (unit, string) result Cmd.t =
  let default = Term.(ret (const (`Help (`Pager, Some "convert")))) in
  Cmd.(
    group ~default (info ~doc:"Convert between trace formats." "convert") [ Native.cmd ])
;;
