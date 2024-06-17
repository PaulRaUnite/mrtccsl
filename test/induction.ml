open Mrtccsl
open Prelude
open Rtccsl
open Analysis

let example1 d1 d2 =
  ( []
  , [ RTdelay { out = "l"; arg = "in"; delay = TimeConst d1, TimeConst d1 }
    ; RTdelay { out = "r"; arg = "in"; delay = TimeConst d2, TimeConst d2 }
    ]
  , [ Precedence { cause = "l"; effect = "r" } ] )
;;

let example2 =
  ( []
  , [ RTdelay { out = "d"; arg = "e"; delay = TimeConst 1, TimeConst 1 }
    ; CumulPeriodic
        { out = "b"
        ; period = TimeConst 50
        ; error = TimeConst (-2), TimeConst 2
        ; offset = TimeConst 1
        }
    ; Sample { out = "s"; arg = "d"; base = "b" }
    ]
  , [] )
;;

let example3 d1 d2 t =
  let d1 = Tuple.map2 (fun v -> TimeConst v) d1 in
  let d2 = Tuple.map2 (fun v -> TimeConst v) d2 in
  let t = Tuple.map2 (fun v -> TimeConst v) t in
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
        ; period = TimeConst 50
        ; error = TimeConst (-2), TimeConst 2
        ; offset =
            (let x, y = d1 in
             TimeConst (Int.max x y + 3))
        }
    ]
  , [ RTdelay { out = "b"; arg = "a"; delay = Tuple.map2 (fun v -> TimeConst v) d1 }
    ; Delay { out = "d"; arg = "b"; delay = IntConst n, IntConst n; base = Some "base" }
    ; RTdelay { out = "e"; arg = "d"; delay = Tuple.map2 (fun v -> TimeConst v) d2 }
    ; FirstSampled { out = "fb"; arg = "b"; base = "base" }
    ; RTdelay { out = "fb"; arg = "fa"; delay = Tuple.map2 (fun v -> TimeConst v) d1 }
      (* ; Causality { cause = "fa"; effect = "fb" } *)
    ; Subclocking { sub = "fa"; super = "a" }
    ; RTdelay { out = "fad"; arg = "fa"; delay = TimeConst t, TimeConst t }
    ]
  , [ Precedence { cause = "e"; effect = "fad" } ] )
;;

let example5 =
  ( []
  , [ RTdelay { out = "l"; arg = "in"; delay = TimeConst 1, TimeConst 2 }
    ; RTdelay { out = "r"; arg = "in"; delay = TimeConst 3, TimeConst 4 }
    ]
  , [ Fastest { out = "f"; left = "l"; right = "r" }
    ; Precedence { cause = "f"; effect = "r" }
    ] )
;;

let trivial = [], [], []

let example6 n =
  ( []
  , [ Sample { out = "c"; arg = "b"; base = "base" }
    ; Delay { out = "d"; arg = "c"; delay = IntConst n, IntConst n; base = Some "base" }
    ]
  , [ Delay { out = "d"; arg = "b"; delay = IntConst n, IntConst n; base = Some "base" } ]
  )
;;

let example7 period n1 n2 d =
  ( [ CumulPeriodic
        { out = "base"
        ; period = TimeConst period
        ; error = TimeConst (-2), TimeConst 2
        ; offset = TimeConst 10
        }
    ]
  , [ Delay { out = "b"; arg = "a"; delay = IntConst n1, IntConst n1; base = Some "base" }
    ; RTdelay { out = "c"; arg = "b"; delay = TimeConst d, TimeConst d }
    ; Delay
        { out = "dbase"
        ; arg = "base"
        ; delay = IntConst (n1 + 1), IntConst (n1 + 1)
        ; base = None
        }
    ; Delay
        { out = "d"; arg = "c"; delay = IntConst n2, IntConst n2; base = Some "dbase" }
    ]
  , [] )
;;

let param1 d1 d2 n t1 t2 =
  let t = "t" in
  ( [ CumulPeriodic
        { out = "base"
        ; period = TimeConst 50
        ; error = TimeConst (-2), TimeConst 2
        ; offset =
            (let x, y = d1 in
             TimeConst (Int.max x y + 3))
        }
    ]
  , [ RTdelay { out = "b"; arg = "a"; delay = Tuple.map2 (fun v -> TimeConst v) d1 }
    ; Delay { out = "d"; arg = "b"; delay = IntConst n, IntConst n; base = Some "base" }
    ; RTdelay { out = "e"; arg = "d"; delay = Tuple.map2 (fun v -> TimeConst v) d2 }
    ; FirstSampled { out = "fb"; arg = "b"; base = "base" }
    ; RTdelay { out = "fb"; arg = "fa"; delay = Tuple.map2 (fun v -> TimeConst v) d1 }
      (* ; Causality { cause = "fa"; effect = "fb" } *)
    ; Subclocking { sub = "fa"; super = "a" }
    ]
  , [ Precedence { cause = "e"; effect = "fad" }
    ; TimeParameter (t, (Const t1, Const t2))
    ; RTdelay { out = "fad"; arg = "fa"; delay = TimeVar t, TimeVar t }
    ] )
;;

let inclusion (a, b) (c, d) =
  ( []
  , [ TimeParameter ("x", (Const a, Const b)) ]
  , [ TimeParameter ("x", (Const c, Const d)) ] )
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
    ; "example1", cases [ "+d1=1,d2=2", example1 1 2, Result true ]
    ; "example2", cases [ "", example2, Result true ]
    ; ( "example3"
      , cases
          [ "+d1=[1,2],d2=[2,3],t=[3,3]", example3 (1, 2) (2, 3) (3, 3), Result true
          ; "-d1=[1,2],d2=[2,3],t=[2,2]", example3 (1, 2) (2, 3) (2, 2), Result false
          ] )
    ; ( "example4"
      , cases
          [ "t=600", example4 (3, 3) (3, 3) 4 600, Result true
          ; "t=200", example4 (3, 3) (3, 3) 4 200, Result false
          ] )
    ; "example5", cases [ "", example5, Result true ]
    ; "example6", cases [ "", example6 2, Result true ]
    ; "example7", cases [ "", example7 10 2 3 5, Crash I.ProductLoop ]
    ; ( "param1"
      , cases
          [ "t=[600,1000]", param1 (3, 3) (3, 3) 4 600 1000, Result true
          ; "t=[200,300]", param1 (3, 3) (3, 3) 4 200 300, Result false
          ] )
    ; ( "pure_params"
      , cases
          [ "[100, 200] <= [100,400]", inclusion (100, 200) (100, 400), Result true
          ;"[100, 200] <= [100,400]", inclusion (100, 100) (100, 100), Result true
          ; "[100, 200] !<= [200,400]", inclusion (100, 200) (200, 400), Result false
          ] )
    ]
;;
