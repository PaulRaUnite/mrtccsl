open Cmdliner
open Cmdliner.Term.Syntax
open Common

let spec_file_arg =
  Arg.(
    required
    & pos 0 (some non_dir_file) None
    & info [] ~doc:"Path to specification file." ~docv:"SPEC")
;;

let cmd : (unit, string) result Cmd.t =
  Cmd.v (Cmd.info "inspect" ~version ~doc:"Format a CCSL+ specification.")
  @@ Term.ret
  @@ let+ specification = spec_file_arg in
     let context, m =
       Mrtccslparsing.load_with_string specification Format.err_formatter
     in
     Mrtccslparsing.Compile.Context.pp Format.std_formatter context;
     let s = Format.pp_print_string
     and r = Number.Rational.pp in
     let open Mrtccsl.Language in
     Module.pp s s s s s r Format.std_formatter m;
     Format.printf
       "\nconstraints: %i, clocks: %i\n"
       (Module.length m)
       (List.length @@ List.sort_uniq String.compare @@ Module.clocks m);
     `Ok (Ok ())
;;
