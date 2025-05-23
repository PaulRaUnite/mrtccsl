open Mrtccsl
open Prelude
open Rtccsl
open Analysis

let time_const_interval = Tuple.map2 (fun v -> Const v)

(**brake-by-wire: static check*)
let example1 d1 d2 =
  ( constraints_only []
  , { constraints =
        [ RTdelay { out = "l"; arg = "in"; delay = "del1" }
        ; RTdelay { out = "r"; arg = "in"; delay = "del2" }
        ]
    ; var_relations =
        [ TimeVarRelation ("del1", Eq, Const d1); TimeVarRelation ("del2", Eq, Const d2) ]
    }
  , constraints_only [ Precedence { cause = "l"; conseq = "r" } ] )
;;

(**Sampling on relatively periodic clock*)
let example2 =
  ( { constraints = [ CumulPeriodic { out = "b"; period = "period"; offset = Const 5 } ]
    ; var_relations =
        [ TimeVarRelation ("period", LessEq, Const 52)
        ; TimeVarRelation ("period", MoreEq, Const 48)
        ]
    }
  , { constraints =
        [ RTdelay { out = "d"; arg = "e"; delay = "del" }
        ; Sample { out = "s"; arg = "d"; base = "b" }
        ]
    ; var_relations = [ TimeVarRelation ("del", Eq, Const 1) ]
    }
  , empty )
;;

(**brake-by-wire: main idea*)
let example3 d1 d2 t =
  ( empty
  , { constraints =
        [ RTdelay { out = "l"; arg = "in"; delay = "del1" }
        ; RTdelay { out = "r"; arg = "in"; delay = "del2" }
        ; Fastest { out = "f"; left = "l"; right = "r" }
        ; Slowest { out = "s"; left = "l"; right = "r" }
        ; RTdelay { out = "d"; arg = "f"; delay = "del3" }
        ]
    ; var_relations =
        (let d11, d12 = d1 in
         let d21, d22 = d2 in
         let t1, t2 = t in
         [ TimeVarRelation ("del1", LessEq, Const d12)
         ; TimeVarRelation ("del1", MoreEq, Const d11)
         ; TimeVarRelation ("del2", LessEq, Const d22)
         ; TimeVarRelation ("del2", MoreEq, Const d21)
         ; TimeVarRelation ("del3", LessEq, Const t2)
         ; TimeVarRelation ("del3", MoreEq, Const t1)
         ])
    }
  , constraints_only [ Precedence { cause = "s"; conseq = "d" } ] )
;;

let example4 d1 d2 n t =
  ( { constraints =
        [ CumulPeriodic
            { out = "base"
            ; period = "period"
            ; offset =
                (let x, y = d1 in
                 Const (Int.max x y + 3))
            }
        ]
    ; var_relations =
        [ TimeVarRelation ("period", LessEq, Const 52)
        ; TimeVarRelation ("period", MoreEq, Const 48)
        ]
    }
  , { constraints =
        [ RTdelay { out = "b"; arg = "a"; delay = "del1" }
        ; Delay { out = "d"; arg = "b"; delay = Const n, Const n; base = Some "base" }
        ; RTdelay { out = "e"; arg = "d"; delay = "del2" }
        ; FirstSampled { out = "fb"; arg = "b"; base = "base" }
        ; RTdelay { out = "fb"; arg = "fa"; delay = "del3" }
          (* ; Causality { cause = "fa"; conseq = "fb" } *)
        ; Subclocking { sub = "fa"; super = "a" }
        ; RTdelay { out = "fad"; arg = "fa"; delay = "del4" }
        ]
    ; var_relations =
        (let d11, d12 = d1 in
         let d21, d22 = d2 in
         [ TimeVarRelation ("del1", LessEq, Const d12)
         ; TimeVarRelation ("del1", MoreEq, Const d11)
         ; TimeVarRelation ("del2", LessEq, Const d22)
         ; TimeVarRelation ("del2", MoreEq, Const d21)
         ; TimeVarRelation ("del3", LessEq, Const d12)
         ; TimeVarRelation ("del3", MoreEq, Const d11)
         ; TimeVarRelation ("del4", Eq, Const t)
         ])
    }
  , constraints_only [ Precedence { cause = "e"; conseq = "fad" } ] )
;;

let example5 =
  ( empty
  , { constraints =
        [ RTdelay { out = "l"; arg = "in"; delay = "del1" }
        ; RTdelay { out = "r"; arg = "in"; delay = "del2" }
        ]
    ; var_relations =
        [ TimeVarRelation ("del1", LessEq, Const 2)
        ; TimeVarRelation ("del1", MoreEq, Const 1)
        ; TimeVarRelation ("del2", LessEq, Const 4)
        ; TimeVarRelation ("del2", MoreEq, Const 3)
        ]
    }
  , constraints_only
      [ Fastest { out = "f"; left = "l"; right = "r" }
      ; Precedence { cause = "f"; conseq = "r" }
      ] )
;;

let trivial = empty, empty, empty

let example6 n =
  ( empty
  , constraints_only
      [ Sample { out = "c"; arg = "b"; base = "base" }
      ; Delay { out = "d"; arg = "c"; delay = Const n, Const n; base = Some "base" }
      ]
  , constraints_only
      [ Delay { out = "d"; arg = "b"; delay = Const n, Const n; base = Some "base" } ] )
;;

let example7 period n1 n2 d =
  ( { constraints = [ CumulPeriodic { out = "base"; period = "period"; offset = Const 10 } ]
    ; var_relations =
        [ TimeVarRelation ("period", LessEq, Const (period + 2))
        ; TimeVarRelation ("period", MoreEq, Const (period - 2))
        ]
    }
  , { constraints =
        [ Delay { out = "b"; arg = "a"; delay = Const n1, Const n1; base = Some "base" }
        ; RTdelay { out = "c"; arg = "b"; delay = "del" }
        ; Delay
            { out = "dbase"
            ; arg = "base"
            ; delay = Const (n1 + 1), Const (n1 + 1)
            ; base = None
            }
        ; Delay { out = "d"; arg = "c"; delay = Const n2, Const n2; base = Some "dbase" }
        ]
    ; var_relations = [ TimeVarRelation ("del", Eq, Const d) ]
    }
  , empty )
;;

let example8 n1 n2 =
  ( []
  , [ Delay { out = "b"; arg = "a"; delay = Const n1, Const n1; base = Some "base" }
    ; Delay { out = "c"; arg = "b"; delay = Const n2, Const n2; base = Some "base" }
    ]
  , [] )
;;

let example9 n1 n2 =
  ( empty
  , constraints_only
      [ Delay { out = "b"; arg = "a"; delay = Const n1, Const n1; base = Some "base" }
      ; Delay
          { out = "dbase"
          ; arg = "base"
          ; delay = Const (n1 + 1), Const (n1 + 1)
          ; base = None
          }
      ; Delay { out = "c"; arg = "b"; delay = Const n2, Const n2; base = Some "dbase" }
      ]
  , empty )
;;

let param1 d1 d2 n t1 t2 =
  ( { constraints =
        [ CumulPeriodic
            { out = "base"
            ; period = "period"
            ; offset =
                (let x, y = d1 in
                 Const (Int.max x y + 3))
            }
        ]
    ; var_relations =
        [ TimeVarRelation ("period", LessEq, Const 52)
        ; TimeVarRelation ("period", MoreEq, Const 48)
        ]
    }
  , { constraints =
        [ RTdelay { out = "b"; arg = "a"; delay = "del1" }
        ; Delay { out = "d"; arg = "b"; delay = Const n, Const n; base = Some "base" }
        ; RTdelay { out = "e"; arg = "d"; delay = "del2" }
        ; FirstSampled { out = "b"; arg = "b"; base = "base" }
        ]
    ; var_relations =
        (let d11, d12 = d1 in
         let d21, d22 = d2 in
         [ TimeVarRelation ("del1", LessEq, Const d12)
         ; TimeVarRelation ("del1", MoreEq, Const d11)
         ; TimeVarRelation ("del2", LessEq, Const d22)
         ; TimeVarRelation ("del2", MoreEq, Const d21)
         ])
    }
  , { constraints =
        [ RTdelay { out = "e"; arg = "a"; delay = "t" }
        ]
    ; var_relations =
        [ TimeVarRelation ("t", LessEq, Const t2)
        ; TimeVarRelation ("t", MoreEq, Const t1)
        ]
    } )
;;

let inclusion (a, b) (c, d) =
  ( empty
  , { constraints = []
    ; var_relations =
        [ TimeVarRelation ("x", MoreEq, Const a); TimeVarRelation ("x", LessEq, Const b) ]
    }
  , { constraints = []
    ; var_relations =
        [ TimeVarRelation ("x", MoreEq, Const c); TimeVarRelation ("x", LessEq, Const d) ]
    } )
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
      (* let _ = Option.iter I.Simulation.print_solution_graph solution.structure_in_property in *)
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

let _ =
  Alcotest.run
    "Inductive proofs"
    [ "trivial", cases [ "", trivial, Result true ]
    ; "example1", cases [ "+d1=1,d2=2", example1 1 2, Result true ]
    ; "example2", cases [ "", example2, Result true ]
    ; ( "example3"
      , cases
          [ "+d1=[1,2],d2=[2,3],t=3", example3 (1, 2) (2, 3) (3, 3), Result true
            (* FIXME: incorrect because of the disjunctions in min/max, they cause
               ; "-d1=[1,2],d2=[2,3],t=2", example3 (1, 2) (2, 3) (2, 2), Result false
               ; "-d1=[2,4],d2=[2,4],t=1", example3 (2, 4) (2, 4) (1,1), Result false *)
          ] )
    ; ( "example4"
      , cases
          [ "t=600", example4 (3, 3) (3, 3) 4 600, Result true
          ; "t=200", example4 (3, 3) (3, 3) 4 200, Result false
          ] )
    ; "example5", cases [ "", example5, Result true ]
    ; "example6", cases [ "", example6 2, Result true ]
    ; "example7", cases [ "", example7 10 2 3 5, Crash I.ProductLoop ]
      (* ; "example8", cases [ "", example8 2 3, Result true ] *)
    ; "example9", cases [ "", example9 2 3, Crash I.ProductLoop ]
    ; ( "param1"
      , cases
          [ 
            (* "t=[246,1000]", param1 (3, 3) (3, 3) 4 246 1000, Result true ; FIXME: no idea what is the problem, but the reason is somewhere in this commit changes.  *)
          "t=[100,245]", param1 (3, 3) (3, 3) 4 100 245, Result false
            (*LIMITATION: parameter is NOT common to all parts, i.e. allowed parameters can be different in different parts, breaking induction. *)
            (* ; "t=[100,300]", param1 (3, 3) (3, 3) 4 100 300, Result true *)
          ] )
    ; ( "pure_params"
      , cases
          [ "[100, 200] <= [100,400]", inclusion (100, 200) (100, 400), Result true
          ; "[100, 100] <= [100,100]", inclusion (100, 100) (100, 100), Result true
          ; "[100, 200] !<= [200,400]", inclusion (100, 200) (200, 400), Result false
          ] )
    ]
;;
