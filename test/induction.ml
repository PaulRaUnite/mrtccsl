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

let example4 d1 d2 n t =
  ( [ CumulPeriodic { out = "base"; period = 50; error = -2, 2; offset = 1 } ]
  , [ RTdelay { out = "b"; arg = "a"; delay = d1 }
    ; Delay { out = "d"; arg = "b"; delay = n, n; base = Some "base" }
    ; RTdelay { out = "e"; arg = "d"; delay = d2 }
    ]
  , [ FirstSampled { out = "fb"; arg = "b"; base = "base" }
    ; Precedence { cause = "fa"; effect = "fb" }
    ; Subclocking { sub = "fa"; super = "a" }
    ; RTdelay { out = "fad"; arg = "fa"; delay = t, t }
    ; Precedence { cause = "e"; effect = "fad" }
    ] )
;;

let test_example d1 d2 n t =
  ( []
  , [ CumulPeriodic { out = "base"; period = 50; error = -2, 2; offset = 1 }
    ; RTdelay { out = "b"; arg = "a"; delay = d1 }
    ; Delay { out = "d"; arg = "b"; delay = n, n; base = Some "base" }
    ; RTdelay { out = "e"; arg = "d"; delay = d2 }
    ; FirstSampled { out = "fb"; arg = "b"; base = "base" }
    ; Precedence { cause = "fa"; effect = "fb" }
    ; Subclocking { sub = "fa"; super = "a" }
    ; RTdelay { out = "fad"; arg = "fa"; delay = t, t }
    ; Precedence { cause = "e"; effect = "fad" }
    ]
  , [] )
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

let trivial = [], [], []

let example6 n =
  ( []
  , [ Sample { out = "c"; arg = "b"; base = "base" }
    ; Delay { out = "d"; arg = "c"; delay = n, n; base = Some "base" }
    ]
  , [ Delay { out = "d"; arg = "b"; delay = n, n; base = Some "base" } ] )
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

let to_alcotest (name, module_triple, expected) =
  let test () =
    let solution = I.Module.solve module_triple in
    let result = I.Module.is_correct solution in
    if not result then I.Module.print solution;
    Alcotest.(check bool) "same result" expected result
  in
  Alcotest.(test_case name `Quick) test
;;

let cases = List.map to_alcotest
let tests = []

let _ =
  Alcotest.run
    "Inductive proofs"
    [ "trivial", cases [ "", trivial, true ]
    ; "test", cases [ "", test_example (2, 2) (3, 3) 2 300, true ]
    ; "example1", cases [ "+d1=1,d2=2", example1 (1, 1) (2, 2), true ]
    ; "example2", cases [ "+v", example2, true; "+^", example2, true ]
    ; ( "example3"
      , cases
          [ "+d1=[1,2],d2=[2,3],t=[3,3]", example3 (1, 2) (2, 3) (3, 3), true
          ; "-d1=[1,2],d2=[2,3],t=[2,2]", example3 (1, 2) (2, 3) (2, 2), false
          ] )
    ; "example4", cases [ "", example4 (2, 2) (3, 3) 2 300, true ]
    ; "example5", cases [ "", example5, true ]
    ; "example6", cases [ "", example6 2, true ]
    ]
;;
