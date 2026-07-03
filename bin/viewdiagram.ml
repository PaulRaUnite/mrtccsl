(* module Q = Common.Number.Rational *)
open Common
open Prelude
open Cmdliner
open Cmdliner.Term.Syntax
open Aux

let spec_file_arg =
  Arg.(
    required
    (* TODO: make it possible to use stdin (need modifications to parsing and its error reporting) *)
    & pos 0 (some non_dir_file) None
    & info [] ~doc:"Path to specification file." ~docv:"SPEC")
;;

let output_arg =
  Arg.(
    value
    & opt (some inline_out_channel) None
    & info
        [ "o"; "output" ]
        ~doc:"Output DOT file. Skip or use - to indicate stdout."
        ~docv:"OUTPUT")
;;

let simulation_flag =
  Arg.(
    value
    & flag
    & info
        [ "s"; "sim" ]
        ~doc:
          "Makes diagram for simulation. By default constructs diagram for acceptance \
           checking.")
;;

let make_diagram simulation spec_filename output =
  let _ = Bdd.init () in
  let open Mrtccsl in
  let _, m = Mrtccslparsing.load_with_string spec_filename Format.err_formatter in
  let spec = Mrtccsl.CCSL.Language.Module.flatten m in
  let open STS.Interpretation.Diagram in
  let d, cstr_index =
    if simulation
    then (
      let clocks =
        List.sort_uniq String.compare (CCSL.Language.Specification.clocks spec)
      in
      let now, m, cstr_index = Backend.Machine.Literal.of_spec spec in
      simulation_diagram now m clocks cstr_index)
    else (
      let now, m, cstr_index = Backend.Machine.Literal.of_spec spec in
      let open STS.Interpretation.Diagram in
      acceptance_diagram now m cstr_index)
  in
  Dot.output_graph output @@ to_graph ~cstr_index d
;;

let cmd : (unit, string) result Cmd.t =
  Cmd.v (Cmd.info "diagram" ~doc:"Visualize a BDD diagram of the specification.")
  @@ Term.ret
  @@ let+ spec_filename = spec_file_arg
     and+ simulation = simulation_flag
     and+ output = output_arg in
     let output = Option.map_or ~default:stdout get_out_channel output in
     `Ok (Ok (make_diagram simulation spec_filename output))
;;
