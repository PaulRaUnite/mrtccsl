open Prelude

let files_to_check =
  [ "empty.mrtccsl"
  ; "with_constraints.mrtccsl"
  ; "hal4sdv.mrtccsl"
  ; "with_constraints_variables_only.mrtccsl"
  ]
;;

let _ =
  Ocolor_format.prettify_formatter Format.std_formatter;
  List.iter
    (fun name ->
       Printf.printf "testing file: %s\n" name;
       let path = Printf.sprintf "code/%s" name in
       let result = Mrtccslparsing.Parse.from_file path in
       let module_dec =
         match result with
         | Ok x -> x
         | Error msg ->
           msg Format.std_formatter ();
           Format.print_flush ();
           failwith "test failed in parsing"
       in
       let context, _, errors = Mrtccslparsing.Compile.into_module module_dec in
       Format.printf "%a\n" Mrtccslparsing.Compile.Context.pp context;
       if not (List.is_empty errors)
       then (
         List.iter
           (Mrtccslparsing.Compile.print_compile_error Format.std_formatter)
           errors;
         failwith "test failed in compilation"))
    files_to_check
;;
