open Mrtccsl
open Prelude
open Analysis
open Denotational.MakeDebug (String) (Number.Integer)
module P = Induction.Make (String) (Number.Integer)

(* module D =
   Induction.PolkaDomain
   (struct
   type dom = Polka.strict Polka.t

   let alloc = Polka.manager_alloc_strict ()
   end)
   (String)
   (Number.Integer) *)
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
        RTdelay { out = "l"; arg = "in"; delay = 1, 2 }
       ; RTdelay { out = "r"; arg = "in"; delay = 3, 4 }
      (* ; Precedence { cause = "ts"; effect = "tf" } *)
        (* ; Precedence { cause = "tf"; effect = "ts" } *)
        (* ; Delay { out = "out"; arg = "in"; delay = 2, 2; base = None } *)
        (* ; Sporadic {out="in"; at_least = 5; strict=true} *)
        ; Fastest {out="f"; left="l"; right="r"}
        ; Precedence {cause=""; effect="r"}
      ]
  in
  (* let pre = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1)) in
  let bottom = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1) && TagVar("a", 1) < TagVar("a", 1)) in
  let _ = Printf.printf "satisfies? %b\n" (S.more_precise pre bottom); Printf.printf "%s\n" (S.to_string bottom) in *)
  let denot_formulae = List.map P.exact_rel spec in
  Printf.printf "Original formulae:\n";
  let _ =
    List.iteri
      (fun i f -> Printf.printf "%i: %s\n" i (string_of_bool_expr f))
      denot_formulae
  in
  let sol = E.solve denot_formulae in
  let problems = E.report sol in
  E.print_problems sol problems
;;
