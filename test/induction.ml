open Mrtccsl
open Prelude
open Language
open Specification.Builder
open Analysis

let time_const_interval = Tuple.map2 (fun v -> Const v)

(**brake-by-wire: static check*)
let example1 d1 d2 =
  Module.make
    []
    (fun b ->
       logical b @@ RTdelay { out = "l"; arg = "in"; delay = Var "del1" };
       logical b @@ RTdelay { out = "r"; arg = "in"; delay = Var "del2" };
       duration b @@ NumRelation ("del1", `Eq, Const d1);
       duration b @@ NumRelation ("del2", `Eq, Const d2))
    []
;;

(**Sampling on relatively periodic clock*)
let example2 =
  Module.make
    [ (fun b ->
        logical b
        @@ CumulPeriodic { out = "b"; period = 50; error = Var "error"; offset = Const 5 };
        duration b @@ NumRelation ("error", `LessEq, Const (2));
        duration b @@ NumRelation ("error", `MoreEq, Const (-2)))
    ]
    (fun b ->
       logical b @@ RTdelay { out = "d"; arg = "e"; delay = Var "del" };
       logical b @@ Sample { out = "s"; arg = "d"; base = "b" };
       duration b @@ NumRelation ("del", `Eq, Const 1))
    []
;;

(**brake-by-wire: main idea*)
let example3 d1 d2 t =
  Module.make
    []
    (fun b ->
       logical b @@ RTdelay { out = "l"; arg = "in"; delay = var "del1" };
       logical b @@ RTdelay { out = "r"; arg = "in"; delay = var "del2" };
       logical b @@ Fastest { out = "f"; args = [ "l"; "r" ] };
       logical b @@ Slowest { out = "s"; args = [ "l"; "r" ] };
       logical b @@ RTdelay { out = "d"; arg = "f"; delay = var "del3" };
       let d11, d12 = d1 in
       let d21, d22 = d2 in
       let t1, t2 = t in
       duration b @@ NumRelation ("del1", `LessEq, Const d12);
       duration b @@ NumRelation ("del1", `MoreEq, Const d11);
       duration b @@ NumRelation ("del2", `LessEq, Const d22);
       duration b @@ NumRelation ("del2", `MoreEq, Const d21);
       duration b @@ NumRelation ("del3", `LessEq, Const t2);
       duration b @@ NumRelation ("del3", `MoreEq, Const t1))
    [ (fun b -> logical b @@ Precedence { cause = "s"; conseq = "d" }) ]
;;

let example4 d1 d2 n t =
  Module.make
    [ (fun b ->
        logical b
        @@ CumulPeriodic
             { out = "base"
             ; period = 50
             ; error = var "error"
             ; offset =
                 (let x, y = d1 in
                  Const (Int.max x y + 3))
             };
        duration b @@ NumRelation ("error", `LessEq, Const 2);
        duration b @@ NumRelation ("error", `MoreEq, Const (-2)))
    ]
    (fun b ->
       logical b @@ RTdelay { out = "b"; arg = "a"; delay = var "del1" };
       logical b @@ Delay { out = "d"; arg = "b"; delay = Const n; base = Some "base" };
       logical b @@ RTdelay { out = "e"; arg = "d"; delay = var "del2" };
       logical b @@ FirstSampled { out = "fb"; arg = "b"; base = "base" };
       logical b @@ RTdelay { out = "fb"; arg = "fa"; delay = var "del3" }
       (* ; Causality { cause = "fa"; conseq = "fb" } *);
       logical b @@ Subclocking { sub = "fa"; super = "a"; dist = None };
       logical b @@ RTdelay { out = "fad"; arg = "fa"; delay = var "del4" };
       let d11, d12 = d1 in
       let d21, d22 = d2 in
       duration b @@ NumRelation ("del1", `LessEq, Const d12);
       duration b @@ NumRelation ("del1", `MoreEq, Const d11);
       duration b @@ NumRelation ("del2", `LessEq, Const d22);
       duration b @@ NumRelation ("del2", `MoreEq, Const d21);
       duration b @@ NumRelation ("del3", `LessEq, Const d12);
       duration b @@ NumRelation ("del3", `MoreEq, Const d11);
       duration b @@ NumRelation ("del4", `Eq, Const t))
    [ (fun b -> logical b @@ Precedence { cause = "e"; conseq = "fad" }) ]
;;

let example5 =
  Module.make
    []
    (fun b ->
       logical b @@ RTdelay { out = "l"; arg = "in"; delay = var "del1" };
       logical b @@ RTdelay { out = "r"; arg = "in"; delay = var "del2" };
       duration b @@ NumRelation ("del1", `LessEq, Const 2);
       duration b @@ NumRelation ("del1", `MoreEq, Const 1);
       duration b @@ NumRelation ("del2", `LessEq, Const 4);
       duration b @@ NumRelation ("del2", `MoreEq, Const 3))
    [ (fun b ->
        logical b @@ Fastest { out = "f"; args = [ "l"; "r" ] };
        logical b @@ Precedence { cause = "f"; conseq = "r" })
    ]
;;

let trivial = Module.empty

let example6 n =
  Module.
    { assumptions = []
    ; structure =
        constraints_only
          [ Sample { out = "c"; arg = "b"; base = "base" }
          ; Delay { out = "d"; arg = "c"; delay = Const n; base = Some "base" }
          ]
    ; assertions =
        [ constraints_only
            [ Delay { out = "d"; arg = "b"; delay = Const n; base = Some "base" } ]
        ]
    }
;;

let example7 period n1 n2 d =
  Module.make
    [ (fun b ->
        logical b
        @@ CumulPeriodic { out = "base"; period; error = var "error"; offset = Const 10 };
        duration b @@ NumRelation ("error", `LessEq, Const 2);
        duration b @@ NumRelation ("error", `MoreEq, Const (-2)))
    ]
    (fun b ->
       logical b @@ Delay { out = "b"; arg = "a"; delay = Const n1; base = Some "base" };
       logical b @@ RTdelay { out = "c"; arg = "b"; delay = var "del" };
       logical b
       @@ Delay { out = "dbase"; arg = "base"; delay = Const (n1 + 1); base = None };
       logical b @@ Delay { out = "d"; arg = "c"; delay = Const n2; base = Some "dbase" };
       duration b @@ NumRelation ("del", `Eq, Const d))
    []
;;

let example8 n1 n2 =
  Module.
    { assertions = []
    ; structure =
        constraints_only
          [ Delay { out = "b"; arg = "a"; delay = Const n1; base = Some "base" }
          ; Delay { out = "c"; arg = "b"; delay = Const n2; base = Some "base" }
          ]
    ; assumptions = []
    }
;;

let example9 n1 n2 =
  Module.
    { assertions = []
    ; structure =
        constraints_only
          [ Delay { out = "b"; arg = "a"; delay = Const n1; base = Some "base" }
          ; Delay { out = "dbase"; arg = "base"; delay = Const (n1 + 1); base = None }
          ; Delay { out = "c"; arg = "b"; delay = Const n2; base = Some "dbase" }
          ]
    ; assumptions = []
    }
;;

let param1 d1 d2 n t1 t2 =
  Module.make
    [ (fun b ->
        logical b
        @@ CumulPeriodic
             { out = "base"
             ; period = 50
             ; error = var "error"
             ; offset =
                 (let x, y = d1 in
                  Const (Int.max x y + 3))
             };
        duration b @@ NumRelation ("error", `LessEq, Const 2);
        duration b @@ NumRelation ("error", `MoreEq, Const (-2)))
    ]
    (fun b ->
       logical b @@ RTdelay { out = "b"; arg = "a"; delay = var "del1" };
       logical b @@ Delay { out = "d"; arg = "b"; delay = Const n; base = Some "base" };
       logical b @@ RTdelay { out = "e"; arg = "d"; delay = var "del2" };
       logical b @@ FirstSampled { out = "b"; arg = "b"; base = "base" };
       let d11, d12 = d1 in
       let d21, d22 = d2 in
       duration b @@ NumRelation ("del1", `LessEq, Const d12);
       duration b @@ NumRelation ("del1", `MoreEq, Const d11);
       duration b @@ NumRelation ("del2", `LessEq, Const d22);
       duration b @@ NumRelation ("del2", `MoreEq, Const d21))
    [ (fun b ->
        logical b @@ RTdelay { out = "e"; arg = "a"; delay = var "t" };
        duration b @@ NumRelation ("t", `LessEq, Const t2);
        duration b @@ NumRelation ("t", `MoreEq, Const t1))
    ]
;;

let inclusion (a, b) (c, d) =
  Module.make
    []
    (fun builder ->
       duration builder @@ NumRelation ("x", `MoreEq, Const a);
       duration builder @@ NumRelation ("x", `LessEq, Const b))
    [ (fun builder ->
        duration builder @@ NumRelation ("x", `MoreEq, Const c);
        duration builder @@ NumRelation ("x", `LessEq, Const d))
    ]
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

let to_alcotest (name, module_instance, expected) =
  let test () =
    match expected with
    | Result expected ->
      let solution = I.Module.solve module_instance in
      (* let _ = Option.iter I.Simulation.print_solution_graph solution.structure_in_property in *)
      let result = I.Module.is_correct solution in
      if not result then I.Module.print solution;
      Alcotest.(check bool) "same result" expected result
    | Crash exp ->
      Alcotest.check_raises "" exp (fun () -> ignore (I.Module.solve module_instance))
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
          [ (* "t=[246,1000]", param1 (3, 3) (3, 3) 4 246 1000, Result true ; FIXME: no idea what is the problem, but the reason is somewhere in this commit changes.  *)
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
