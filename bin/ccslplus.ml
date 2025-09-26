open Cmdliner
open Term.Syntax
open Version

let chorus ~count msg =
  for i = 1 to count do
    print_endline msg
  done
;;

let count =
  let doc = "Repeat the message $(docv) times." in
  Arg.(value @@ opt int 10 @@ info [ "c"; "count" ] ~doc ~docv:"COUNT")
;;

let msg =
  let env =
    let doc = "Overrides the default message to print." in
    Cmd.Env.info "CHORUS_MSG" ~doc
  in
  let doc = "The message to print." in
  Arg.(value @@ pos 0 string "Revolt!" @@ info [] ~env ~doc ~docv:"MSG")
;;

let chorus_cmd =
  let doc = "Print a customizable message repeatedly" in
  let man =
    [ `S Manpage.s_bugs; `P "Bug reports at https://github.com/PaulRaUnite/mrtccsl" ]
  in
  Cmd.v (Cmd.info "eccsl" ~version ~doc ~man)
  @@
  let+ count = count
  and+ msg = msg in
  chorus ~count msg
;;

let main () = Cmd.eval chorus_cmd
let () = if !Sys.interactive then () else exit (main ())
