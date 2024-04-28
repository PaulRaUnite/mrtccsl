open Mrtccsl
open Prelude
open Analysis
open Denotational
open MakeDebug (String) (Number.Integer)
module I = Analysis.Induction.Make (String) (Number.Integer)

let _ =
  let spec =
    Rtccsl.
      [ RTdelay { out = "e"; arg = "e"; delay = 1, 2 }
      ; Precedence { cause = "ts"; effect = "tf" }
      ; Delay { out = "o"; arg = "i"; delay = 2, 2; base = None }
      ]
  in
  let denot_formulae = List.map exact_rel spec in
  let init, pre, cond, post = I.proof_obligations denot_formulae in
  Printf.printf "Init cond: \n%s\n" (string_of_bool_expr init);
  Printf.printf "Induction hypothesis: \n%s\n" (string_of_bool_expr pre);
  Printf.printf "Induction step: \n%s\n" (string_of_bool_expr cond);
  Printf.printf "Postcondition: \n%s\n" (string_of_bool_expr post)
;;
