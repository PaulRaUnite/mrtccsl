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

let example7 period n1 n2 d =
  ( (* [ CumulPeriodic { out = "base"; period; error = -2, 2; offset = 10 } ] *) []
  , Rtccsl.
      [ 
        Delay { out = "b"; arg = "a"; delay = n1, n1; base = Some "base" }
      ; RTdelay { out = "c"; arg = "b"; delay = d, d }
      ; Delay { out = "dbase"; arg = "base"; delay = n1, n1; base = None }
      ; Delay { out = "d"; arg = "c"; delay = n2, n2; base = Some "dbase" }
      ]
  , [] )
;;

let _ =
  let open Rtccsl in
  let _, spec, _ = example7 (IntConst 10) (IntConst 2) (IntConst 3) (TimeConst 5) in
  (* let pre = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1)) in
     let bottom = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1) && TagVar("a", 1) < TagVar("a", 1)) in
     let _ = Printf.printf "satisfies? %b\n" (S.more_precise pre bottom); Printf.printf "%s\n" (S.to_string bottom) in *)
  let denot_formulae = List.map I.under_rel_priority_exact spec in
  Printf.printf "Original formulae:\n";
  let _ =
    List.iteri
      (fun i f -> Printf.printf "%i: %s\n" i (string_of_bool_expr f))
      denot_formulae
  in
  let sol = I.Existence.solve_expr denot_formulae in
  let _ = I.Existence.print_solution sol in
  let n = IntConst 2 in
  let spec =
    Rtccsl.
      [ Sample { out = "c"; arg = "b"; base = "base" }
      ; Delay { out = "d"; arg = "c"; delay = n, n; base = Some "base" }
      ]
  in
  let prop =
    Rtccsl.[ Delay { out = "d"; arg = "b"; delay = n, n; base = Some "base" } ]
  in
  let* sol = I.Property.solve spec prop in
  Some (I.Simulation.print sol)
;;
