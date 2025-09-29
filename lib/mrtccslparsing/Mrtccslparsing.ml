open Prelude

let load filename error_ch =
  Ocolor_format.prettify_formatter error_ch;
  let ast =
    Parse.from_file filename
    |> Result.map_error (fun pp_e ->
      fun fmt -> Format.fprintf fmt "Parsing error: %a" pp_e)
    |> Result.unwrap_to_ch ~msg:"Failed in parsing." error_ch
  in
  let context, m, errors = Compile.into_module ast in
  if not (List.is_empty errors)
  then (
    Compile.Context.pp error_ch context;
    List.iter (Compile.print_compile_error error_ch) errors;
    Format.pp_print_flush error_ch ();
    failwith "Compilation error.")
  else m
;;

let load_with_string filename error_ch =
  let m = load filename error_ch in
  let v2s =
    Compile.(
      function
      | Explicit v -> List.to_string ~sep:"." Fun.id v
      | Anonymous i -> Printf.sprintf "anon(%i)" i)
  in
  let m = Mrtccsl.Ccsl.Language.Module.map v2s v2s Fun.id v2s v2s Fun.id m in
  m
;;

module Loc = Loc
module Parse = Parse
module Compile = Compile
module Ast = Ast
