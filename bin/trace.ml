
open Cmdliner

let cmd : (unit, string) result Cmd.t =
  let default = Term.(ret (const (`Help (`Pager, Some "trace")))) in
  Cmd.(
    group ~default (info ~doc:"Operations on traces." "trace") [ Convert.cmd ; Filter.cmd])
;;
