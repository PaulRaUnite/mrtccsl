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

let example d1 d2 n  =
  let open Rtccsl in
  let t = "t" in
  ( empty
  , { constraints =
        [ CumulPeriodic
            { out = "base"
            ; period = "period"
            ; offset =
                (let x, y = d1 in
                 Const (Int.max x y + 3))
            }
        ; RTdelay { out = "b"; arg = "a"; delay = "del_ab" }
        ; Delay { out = "d"; arg = "b"; delay = const n, const n; base = Some "base" }
        ; RTdelay { out = "e"; arg = "d"; delay = "del_" }
        ; FirstSampled { out = "fb"; arg = "b"; base = "base" }
        ; RTdelay { out = "fb"; arg = "fa"; delay = "del_fafb" }
          (* ; Causality { cause = "fa"; conseq = "fb" } *)
        ; Subclocking { sub = "fa"; super = "a" }
        ; Precedence { cause = "e"; conseq = "fad" }
        ; RTdelay { out = "fad"; arg = "fa"; delay = t }
        ]
    ; var_relations =
        (let d11, d12 = d1 in
         let d21, d22 = d2 in
         [ TimeVarRelation ("period", LessEq, Const 52)
         ; TimeVarRelation ("period", MoreEq, Const 48)
         ; TimeVarRelation ("del_ab", LessEq, Const d12)
         ; TimeVarRelation ("del_ab", MoreEq, Const d11)
         ; TimeVarRelation ("del_fafb", LessEq, Const d12)
         ; TimeVarRelation ("del_fafb", MoreEq, Const d11)
         ; TimeVarRelation ("del_de", LessEq, Const d22)
         ; TimeVarRelation ("del_de", MoreEq, Const d21)
         ; TimeVarRelation (t, LessEq, Const 400)
         ; TimeVarRelation (t, MoreEq, Const 250)
         ])
    }
  , empty )
;;

let _ =
  let open Rtccsl in
  let assumption, spec, _ = example (3, 3) (3, 3) 4 in
  (* let pre = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1)) in
     let bottom = S.of_formula Denotational.Syntax.(TagVar ("a", 0) < TagVar("a", 1) && TagVar("a", 1) < TagVar("a", 1)) in
     let _ = Printf.printf "satisfies? %b\n" (S.more_precise pre bottom); Printf.printf "%s\n" (S.to_string bottom) in *)
  let sol = I.Existence.solve (Rtccsl.merge assumption spec) in
  let _ = I.Existence.print sol in
  let variants = I.Existence.extract_params [ "t" ] sol in
  Printf.printf "variants: %i\n" (List.length variants);
  List.print (fun s -> Printf.printf "%s\n" (S.to_string s)) variants
;;
