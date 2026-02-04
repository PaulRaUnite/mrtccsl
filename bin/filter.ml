open Prelude
open Common
open Cmdliner
open Cmdliner.Term.Syntax
open Number

module Label = struct
  include Set.Make (String)
  module E = String
end

module IO = Mrtccsl.Trace.MakeIO (Rational) (Label)

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

let regexps_arg =
  Arg.(
    value
    & opt_all string []
    & info
        [ "r"; "regex" ]
        ~doc:
          "Regular expression to filter out the clocks in a trace. If several are \
           specified, a clock needs to satisfy at least one regex.")
;;

let filter ~regexps input output =
  let clocks, trace = IO.CSV.read input in
  let filter_clock c = List.exists (fun r -> Str.string_match r c 0) regexps in
  let clocks = List.filter filter_clock clocks in
  let open Mrtccsl.Trace in
  let filter_step { label; time } =
    let label = Label.filter filter_clock label in
    if Label.is_empty label then None else Some { label; time }
  in
  IO.CSV.write output clocks (Seq.filter_map filter_step trace)
;;

let cmd : (unit, string) result Cmd.t =
  Cmd.v (Cmd.info "filter" ~doc:"Filter out clocks using an OCaml regexp.")
  @@ Term.ret
  @@ let+ input = input_arg
     and+ output = output_arg
     and+ regexps = regexps_arg in
     let input = Option.map_or ~default:stdin get_in_channel input
     and output = Option.map_or ~default:stdout get_out_channel output
     and regexps = List.map Str.regexp regexps in
     `Ok (Ok (filter ~regexps input output))
;;
