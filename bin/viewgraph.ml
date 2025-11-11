open Prelude
open Common
open Cmdliner
open Cmdliner.Term.Syntax

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

let make_graph spec_filename output =
  let _, m = Mrtccslparsing.load_with_string spec_filename Format.err_formatter in
  (*TODO: remove flattening*)
  let spec = Mrtccsl.Language.Module.flatten m in
  let open Mrtccsl.Ccsl.View.AsDefined in
  let graph = of_spec Fun.id spec in
  G.iter_vertex
    (fun v ->
       match G.in_degree graph v with
       | 0 ->
         (match G.V.label v with
          | Clock c -> Printf.printf "free clock %s\n" c
          | Constraint c -> Printf.printf "free constraint: %s\n" c)
       | 1 -> ()
       | _ ->
         (match G.V.label v with
          | Clock c -> Printf.printf "conflict definition in clock %s\n" c
          | _ -> ()))
    graph;
  Dot.output_graph output graph
;;

let cmd : (unit, string) result Cmd.t =
  Cmd.v (Cmd.info "view" ~doc:"Visualize a specification.")
  @@ Term.ret
  @@ let+ spec_filename = spec_file_arg
     and+ output = output_arg in
     let output = Option.map_or ~default:stdout get_out_channel output in
     `Ok (Ok (make_graph spec_filename output))
;;
