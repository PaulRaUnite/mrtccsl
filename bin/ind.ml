open Mrtccsl
open Prelude
open Analysis
open Denotational.MakeDebug (String) (Number.Integer)
module P = Induction.Make (String) (Number.Integer)
module D = Induction.VPLDomain (String) (Number.Integer)

module S = P.Solver.MakeFromDomain (struct
    include D

    let index_name = "i"
  end)

module E = P.ExistenceProof (S)

let _ =
  let spec =
    Rtccsl.
      [ 
        (* RTdelay { out = "del"; arg = "in"; delay = 1, 2 }
      ; Precedence { cause = "ts"; effect = "tf" }
        (* ; Precedence { cause = "tf"; effect = "ts" } *)
      ; Delay { out = "out"; arg = "in"; delay = 2, 2; base = None } *)
      Sporadic {out="in"; at_least = 5; strict=true}
      ]
  in
  let denot_formulae = List.map P.exact_rel spec in
  Printf.printf "Original formulae:\n";
  let _ =
    List.iteri
      (fun i f -> Printf.printf "%i: %s\n" i (string_of_bool_expr f))
      denot_formulae
  in
  let sol = E.solve denot_formulae in
  let problems = E.unsolved sol in
  E.print_problems sol problems
;;
