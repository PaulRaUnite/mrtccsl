open Prelude

let files_to_check = [ "empty.mrtccsl"; "with_constraints.mrtccsl"; "hal4sdv.mrtccsl" ]

let _ =
  List.iter
    (fun name ->
       Printf.printf "testing file: %s\n" name;
       let path = Printf.sprintf "code/%s" name in
       let result = Mrtccslparsing.Parse.from_file path in
       let module_dec =
         match result with
         | Ok x -> x
         | Error msg ->
           msg Format.std_formatter;
           Format.print_flush ();
           failwith "test failed"
       in
       match Mrtccslparsing.Compile.into_module module_dec with
       | Ok _, _ -> ()
       | Error e, _ -> Mrtccslparsing.Compile.print_compile_error Format.std_formatter e)
    files_to_check
;;
