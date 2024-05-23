open Mrtccsl
open Prelude
open Analysis
open Denotational.MakeDebug (String) (Number.Integer)
module D = Domain.VPL (String) (Number.Integer)

module S =
  Induction.Solver.MakeFromDomain (String) (Number.Integer)
    (struct
      include D

      let index_name = "i"
    end)

module I = Induction.Make (String) (Number.Integer) (S)

(* module D =
   Induction.PolkaDomain
   (struct
   type dom = Polka.strict Polka.t

   let alloc = Polka.manager_alloc_strict ()
   end)
   (String)
   (Number.Integer) *)

let _ =
  let spec =
    Rtccsl.
      [ RTdelay { out = "l"; arg = "in"; delay = 1, 2 }
      ; RTdelay { out = "r"; arg = "in"; delay = 3, 4 }
        (* ; Precedence { cause = "ts"; effect = "tf" } *)
        (* ; Precedence { cause = "tf"; effect = "ts" } *)
        (* ; Delay { out = "out"; arg = "in"; delay = 2, 2; base = None } *)
        (* ; Sporadic {out="in"; at_least = 5; strict=true} *)
        (* ; Fastest { out = "f"; left = "l"; right = "r" }
      ; Precedence { cause = "f"; effect = "r" } *)
      ]
  in
  (* let pre = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1)) in
     let bottom = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1) && TagVar("a", 1) < TagVar("a", 1)) in
     let _ = Printf.printf "satisfies? %b\n" (S.more_precise pre bottom); Printf.printf "%s\n" (S.to_string bottom) in *)
  let denot_formulae = List.map I.exact_rel spec in
  Printf.printf "Original formulae:\n";
  let _ =
    List.iteri
      (fun i f -> Printf.printf "%i: %s\n" i (string_of_bool_expr f))
      denot_formulae
  in
  let sol = I.Existence.solve_expr denot_formulae in
  let _ = I.Existence.print_solution sol in
  let spec =
    Rtccsl.
      [ RTdelay { out = "l"; arg = "in"; delay = 1, 2 }
      ; RTdelay { out = "r"; arg = "in"; delay = 3, 4 }
      ]
  in
  let prop =
    Rtccsl.
      [ Fastest { out = "f"; left = "l"; right = "r" }
      ; Precedence { cause = "f"; effect = "r" }
      ]
  in
  let* sol = I.Property.solve spec prop in
  Some (I.Simulation.print sol)
;;
