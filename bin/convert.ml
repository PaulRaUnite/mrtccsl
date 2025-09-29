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
  module CSL = struct
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

    let scale_arg =
      Arg.(
        value
        & opt (some rational) None
        & info [ "s"; "scale" ] ~doc:"Discretization scale." ~docv:"SCALE")
    ;;

    let spec_arg =
      Arg.(
        value
        & opt (some non_dir_file) None
        & info
            [ "m"; "microstep" ]
            ~doc:
              "File with specification used to generate the trace. Used to derive \
               microstep ordering."
            ~docv:"MICROSTEP")
    ;;

    let discretization_arg =
      Arg.(
        value
        & opt (some rounding) None
        & info
            [ "d"; "discretize" ]
            ~doc:
              "Rounding type used in discretization. $(docv) is either near, floor or \
               ceil. $(i,SCALE) is required parameter for discretization."
            ~docv:"ROUNDING")
    ;;

    let convert ~serialize ~discretize ~scale input output =
      let serialize =
        Option.map_or
          ~default:FnCh.Export.Inner.Serialize.random
          (fun spec ->
             FnCh.Export.Inner.Serialize.respect_microstep
               (Mrtccsl.Ccsl.MicroStep.derive_order
                  Mrtccsl.Ccsl.Language.Specification.(spec.logical)))
          serialize
      in
      let to_scl =
        Option.map_or
          ~default:(FnCh.Export.trace_to_csl ~tagger:FnCh.Export.Inner.Tag.none)
          (fun rounding ->
             let round = of_rounding rounding in
             let scale = Option.unwrap ~expect:"scale is needed for rounding" scale in
             FnCh.Export.trace_to_csl
               ~tagger:(FnCh.Export.Inner.Tag.tag_round_timestamp (round ~divisor:scale)))
          discretize
      in
      let session = FnCh.S.Session.create () in
      let trace = FnCh.Export.read_csv session input in
      to_scl session ~serialize (Format.formatter_of_out_channel output) trace
    ;;

    let cmd =
      Cmd.(
        v
          (info
             "csl"
             ~doc:
               "Convert native trace into comma-separated list (CSL) of events, possibly \
                with discretized time deltas and respecting microstep ordering inside \
                the CCSL's step.")
        @@ Term.ret
        @@ let+ scale = scale_arg
           and+ input = input_arg
           and+ output = output_arg
           and+ microstep = spec_arg
           and+ discretize = discretization_arg in
           let input = Option.map_or ~default:stdin get_in_channel input
           and output = Option.map_or ~default:stdout get_out_channel output
           and serialize =
             Option.map
               (fun spec_file ->
                  let m =
                    Mrtccslparsing.load_with_string spec_file Format.err_formatter
                  in
                  let spec = Mrtccsl.Ccsl.Language.Module.flatten m in
                  spec)
               microstep
           in
           `Ok (Ok (convert ~discretize ~scale ~serialize input output)))
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
      [ CSL.cmd; SvgBob.cmd ]
  ;;
end

let cmd : (unit, string) result Cmd.t =
  let default = Term.(ret (const (`Help (`Pager, Some "convert")))) in
  Cmd.(
    group ~default (info ~doc:"Convert between trace formats." "convert") [ Native.cmd ])
;;
