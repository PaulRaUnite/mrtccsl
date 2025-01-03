open Mrtccsl
open Prelude

let files_to_check = [ "empty.mrtccsl"; "features.mrtccsl"; "spark-control.mrtccsl"; "bbw.mrtccsl" ;"mlv.mrtccsl" ]

let _ =
  List.iter
    (fun name ->
      Printf.printf "testing file: %s\n" name;
      let path = Printf.sprintf "code/%s" name in
      let _ = Parsing.from_file path in
      ())
    files_to_check
;;
