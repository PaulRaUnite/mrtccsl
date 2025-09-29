let version =
  match Build_info.V1.version () with
  | None -> "dev"
  | Some v -> Build_info.V1.Version.to_string v
;;

let reaction_name dir chain_name span =
  let start, finish = span in
  Printf.sprintf "%s/%s/%s_%s.reaction.csv" dir chain_name start finish
;;

let histogram_name dir chain_name span =
  let start, finish = span in
  Printf.sprintf "%s/%s/%s_%s.histogram.csv" dir chain_name start finish
;;

let rational =
  let parser s =
    try Ok (Number.Rational.of_decimal_string s) with
    | Failure s -> Error (`Msg s)
  and pp ppf x = Format.fprintf ppf "%s" (Number.Rational.to_string x) in
  Cmdliner.Arg.conv (parser, pp)
;;

type in_channel =
  | Stdin
  | File of string

let get_in_channel = function
  | Stdin -> stdin
  | File s -> open_in s
;;

let in_channel_string = function
  | Stdin -> "stdin"
  | File s -> s
;;

type out_channel =
  | Stdout
  | File of string

let get_out_channel = function
  | Stdout -> stdout
  | File s -> open_out s
;;

let out_channel_string = function
  | Stdout -> "stdout"
  | File s -> s
;;

let inline_in_channel =
  let parser = function
    | "-" -> Ok Stdin
    | s -> Ok (File s)
  and pp ppf x = Format.fprintf ppf "%s" (in_channel_string x) in
  Cmdliner.Arg.conv (parser, pp)
;;

let inline_out_channel =
  let parser = function
    | "-" -> Ok Stdout
    | s -> Ok (File s)
  and pp ppf x = Format.fprintf ppf "%s" (out_channel_string x) in
  Cmdliner.Arg.conv (parser, pp)
;;
