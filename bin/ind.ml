open Mrtccsl
open Prelude
open Analysis
open Denotational.MakeDebug (String) (Number.Integer)
module P = Induction.Make (String) (Number.Integer)

let _ =
  let spec =
    Rtccsl.
      [ RTdelay { out = "del"; arg = "in"; delay = 1, 2 }
      ; Precedence { cause = "ts"; effect = "tf" }
      ; Delay { out = "out"; arg = "in"; delay = 2, 2; base = None }
      ]
  in
  let denot_formulae = List.map P.exact_rel spec in
  Printf.printf "Original formulae:\n";
  let _ = List.iteri (fun i f -> Printf.printf "%i: %s\n" i (string_of_bool_expr f)) denot_formulae in
  let init, pre, cond, post = P.Hypothesis.construct denot_formulae in
  Printf.printf "Init cond: \n%s\n" (string_of_bool_expr init);
  Printf.printf "Induction hypothesis: \n%s\n" (string_of_bool_expr pre);
  Printf.printf "Induction step: \n%s\n" (string_of_bool_expr cond);
  Printf.printf "Postcondition: \n%s\n" (string_of_bool_expr post)
;;
