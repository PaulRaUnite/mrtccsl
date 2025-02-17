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

let example d1 d2 n =
  let open Rtccsl in
  let t = "t" in
  ( []
  , [ CumulPeriodic
        { out = "base"
        ; period = TimeConst 50
        ; error = TimeConst (-2), TimeConst 2
        ; offset =
            (let x, y = d1 in
             TimeConst (Int.max x y + 3))
        }
    ; RTdelay { out = "b"; arg = "a"; delay = Tuple.map2 (fun v -> TimeConst v) d1 }
    ; Delay { out = "d"; arg = "b"; delay = IntConst n, IntConst n; base = Some "base" }
    ; RTdelay { out = "e"; arg = "d"; delay = Tuple.map2 (fun v -> TimeConst v) d2 }
    ; FirstSampled { out = "fb"; arg = "b"; base = "base" }
    ; RTdelay { out = "fb"; arg = "fa"; delay = Tuple.map2 (fun v -> TimeConst v) d1 }
      (* ; Causality { cause = "fa"; conseq = "fb" } *)
    ; Subclocking { sub = "fa"; super = "a" }
    ; Precedence { cause = "e"; conseq = "fad" }
    ; TimeParameter (t, (Const 250, Const 400))
    ; RTdelay { out = "fad"; arg = "fa"; delay = TimeVar t, TimeVar t }
    ]
  , [] )
;;

let _ =
  let open Rtccsl in
  let assumption, spec, _ = example (3, 3) (3, 3) 4 in
  (* let pre = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1)) in
     let bottom = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1) && TagVar("a", 1) < TagVar("a", 1)) in
     let _ = Printf.printf "satisfies? %b\n" (S.more_precise pre bottom); Printf.printf "%s\n" (S.to_string bottom) in *)
  let sol = I.Existence.solve (assumption @ spec) in
  let _ = I.Existence.print sol in
  let variants = I.Existence.extract_params [ "t" ] sol in
  Printf.printf "variants: %i\n" (List.length variants);
  List.print (fun s -> Printf.printf "%s\n" (S.to_string s)) variants
;;
