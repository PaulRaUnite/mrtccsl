open Mrtccsl
open Prelude
open Rtccsl
open Analysis

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
  ( [ CumulPeriodic
        { out = "base"
        ; period = 50
        ; error = -2, 2
        ; offset =
            (let x, y = d1 in
             Int.max x y + 3)
        }
    ]
  , [ RTdelay { out = "b"; arg = "a"; delay = d1 }
    ; Delay { out = "d"; arg = "b"; delay = n, n; base = Some "base" }
    ; RTdelay { out = "e"; arg = "d"; delay = d2 }
    ; FirstSampled { out = "fb"; arg = "b"; base = "base" }
    ; RTdelay { out = "fb"; arg = "fa"; delay = d1 }
      (* ; Causality { cause = "fa"; effect = "fb" } *)
    ; Subclocking { sub = "fa"; super = "a" }
    ; RTdelay { out = "fad"; arg = "fa"; delay = t, t }
    ]
  , [ Precedence { cause = "e"; effect = "fad" } ] )
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

let example7 period n1 n2 d =
  ( [ CumulPeriodic { out = "base"; period; error = -2, 2; offset = 10 } ]
  , [ Delay { out = "b"; arg = "a"; delay = n1, n1; base = Some "base" }
    ; RTdelay { out = "c"; arg = "b"; delay = d, d }
    ; Delay { out = "dbase"; arg = "base"; delay = n1 + 1, n1 + 1; base = None }
    ; Delay { out = "d"; arg = "c"; delay = n2, n2; base = Some "dbase" }
    ]
  , [] )
;;

module D = Domain.VPL (String) (Number.Integer)

module S =
  Induction.Solver.MakeFromDomain (String) (Number.Integer)
    (struct
      include D

      let index_name = "i"
    end)

module I = Induction.Make (String) (Number.Integer) (S)

type expectation =
  | Result of bool
  | Crash of exn
  | UnsatAssumption
  | UnsatAssertion

let to_alcotest (name, module_triple, expected) =
  let test () =
    match expected with
    | Result expected ->
      let solution = I.Module.solve module_triple in
      (* let _ = I.Existence.print_report_graph solution.structure in *)
      let result = I.Module.is_correct solution in
      if not result then I.Module.print solution;
      Alcotest.(check bool) "same result" expected result
    | Crash exp ->
      Alcotest.check_raises "" exp (fun () -> ignore (I.Module.solve module_triple))
    | UnsatAssertion | UnsatAssumption -> failwith "not implemented"
  in
  Alcotest.(test_case name `Quick) test
;;

let cases = List.map to_alcotest
let tests = []

let _ =
  Alcotest.run
    "Inductive proofs"
    [ "trivial", cases [ "", trivial, Result true ]
    ; "example1", cases [ "+d1=1,d2=2", example1 (1, 1) (2, 2), Result true ]
    ; "example2", cases [ "", example2, Result true ]
    ; ( "example3"
      , cases
          [ "+d1=[1,2],d2=[2,3],t=[3,3]", example3 (1, 2) (2, 3) (3, 3), Result true
          ; "-d1=[1,2],d2=[2,3],t=[2,2]", example3 (1, 2) (2, 3) (2, 2), Result false
          ] )
    ; "example4", cases [ "", example4 (3, 3) (3, 3) 4 600, Result true ]
    ; "example5", cases [ "", example5, Result true ]
    ; "example6", cases [ "", example6 2, Result true ]
    ; "example7", cases [ "", example7 10 2 3 5, Crash I.ProductLoop ]
    ]
;;
