open Cmdliner

let cmd : (unit, string) result Cmd.t =
  let default = Term.(ret (const (`Help (`Pager, Some "view")))) in
  Cmd.(
    group ~default (info ~doc:"Specification views: links and diagram." "view") [ Viewgraph.cmd ; Viewdiagram.cmd])
;;
