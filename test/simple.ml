open Prelude
open Rtccsl
open Number
module A = Automata.Simple.MakeExtendedString (Rational)

let wall_test spec traces results =
  let check i (case, result) =
    let test () =
      let automaton = A.of_spec spec in
      Alcotest.(check bool) "same result" result
      @@ Option.is_some (A.accept_trace automaton Rational.zero case)
    in
    Alcotest.(test_case (Printf.sprintf "case%i" i) `Quick) test
  in
  List.mapi check (List.combine traces results)
;;

let logical_wall_test spec traces_results =
  let traces, results = List.split traces_results in
  let add_time trace =
    List.combine
      trace
      (List.init (List.length trace) (fun x -> Number.Rational.from_int (x + 1)))
  in
  let traces = List.map add_time traces in
  wall_test spec traces results
;;

let () =
  Alcotest.run
    "Simple Automata"
    [ ( "causality"
      , logical_wall_test
          [ Causality ("a", "b") ]
          [ A.trace_of_regexp "(ab)(ab)(ab)", true
          ; A.trace_of_regexp "bbb", false
          ] )
    ; ( "forbid"
      , logical_wall_test
          [ Forbid ("f", "t", [ "a" ]); Precedence ("f", "a"); Precedence ("a", "t") ]
          [ A.trace_of_regexp "fat", false ] )
    ]
;;
