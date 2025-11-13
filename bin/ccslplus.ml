open Cmdliner
open Common

let cmd =
  let default = Term.(ret (const (`Help (`Pager, None)))) in
  Cmd.group
    ~default
    (Cmd.info
       ~version
       "ccsl+"
       ~doc:"Collection of tools for CCSL+ (modular, real-time, probabilistic CCSL).")
    [ Simulate.cmd; Reaction.cmd; Trace.cmd ; Check.cmd ; Viewgraph.cmd; Debug.cmd]
;;

let main () = Cmd.eval_result cmd
let () = if !Sys.interactive then () else exit (main ())
