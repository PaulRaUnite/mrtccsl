open Mrtccsl
open Prelude
open Rtccsl

let example1 d1 d2 =
  ( []
  , [ RTdelay { out = "l"; arg = "in"; delay = d1 }
    ; RTdelay { out = "r"; arg = "in"; delay = d2 }
    ]
  , [ Precedence { cause = "l"; effect = "r" } ] )
;;

let example2 =
  ( []
  , [ RTdelay { out = "d"; arg = "e"; delay = 1, 1 }
    ; CumulPeriodic { out = "b"; period = 50; error = -2, 2; offset = 1 }
    ; Sample { out = "s"; arg = "d"; base = "b" }
    ]
  , [] )
;;

let example3 d1 d2 t =
  ( []
  , [ RTdelay { out = "l"; arg = "in"; delay = d1 }
    ; RTdelay { out = "r"; arg = "in"; delay = d2 }
    ]
  , [ Fastest { out = "f"; left = "l"; right = "r" }
    ; Slowest { out = "s"; left = "l"; right = "r" }
    ; RTdelay { out = "d"; arg = "f"; delay = t }
    ; Precedence { cause = "s"; effect = "d" }
    ] )
;;

let example4 d1 n t =
  ( [ CumulPeriodic { out = "base"; period = 50; error = -2, 2; offset = 1 } ]
  , [ RTdelay { out = "b"; arg = "e"; delay = d1, d1 }
    ; Sample { out = "c"; arg = "b"; base = "base" }
    ; Delay { out = "d"; arg = "c"; delay = n, n; base = Some "base" }
    ]
  , [ FirstSampled { out = "fb"; arg = "b"; base = "base" }
    ; Precedence { cause = "fa"; effect = "fb" }
    ; Subclocking { sub = "fa"; super = "a" }
    ; RTdelay { out = "fad"; arg = "fa"; delay = t, t }
    ; Precedence { cause = "e"; effect = "fad" }
    ] )
;;

let example5 =
  ( []
  , [ RTdelay { out = "l"; arg = "in"; delay = 1, 2 }
    ; RTdelay { out = "r"; arg = "in"; delay = 3, 4 }
    ]
  , [ Fastest { out = "f"; left = "l"; right = "r" }
    ; Precedence { cause = "f"; effect = "r" }
    ] )
;;

open Analysis
module D = Domain.VPL (String) (Number.Integer)

module S =
  Induction.Solver.MakeFromDomain (String) (Number.Integer)
    (struct
      include D

      let index_name = "i"
    end)

module I = Induction.Make (String) (Number.Integer) (S)

type target =
  | Over
  | Exact
  | Under

let to_alcotest (name, t, (a, s, p), expected) =
  let test () =
    let to_formulae =
      match t with
      | Over -> I.safe_over_rel_spec
      | Under -> I.under_rel_spec
      | Exact -> I.exact_spec
    in
    let a, s, p = Tuple.map3 to_formulae (a, s, p) in
    let assumption_test = I.Property.solve a s in
    let property_test = I.Property.solve (a @ s) p in
    let assumption_correct = I.Property.is_sat assumption_test in
    let property_correct = I.Property.is_sat property_test in
    let result = assumption_correct && property_correct in
    if not result then Printf.printf "a=%b;p=%b" assumption_correct property_correct;
    Alcotest.(check bool) "same result" expected result
  in
  Alcotest.(test_case name `Quick) test
;;

let cases = List.map to_alcotest
let tests = []

let _ =
  Alcotest.run
    "Inductive proofs"
    [ "example1", cases [ "+d1=1,d2=2", Exact, example1 (1, 1) (2, 2), true ]
    ; "example2", cases [ "+v", Under, example2, true; "+^", Over, example2, true ]
    ; ( "example3"
      , cases
          [ "+d1=[1,2],d2=[2,3],t=[3,3]", Exact, example3 (1, 2) (2, 3) (3, 3), true
          ; "-d1=[1,2],d2=[2,3],t=[2,2]", Exact, example3 (1, 2) (2, 3) (2, 2), false
          ] )
    ; "example4", cases [ "", Under, example4 1 2 152, true ]
    ; "example5", cases []
    ]
;;
