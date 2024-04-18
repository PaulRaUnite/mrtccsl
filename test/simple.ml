open Prelude
open Rtccsl
open Number
module A = Automata.Simple.MakeExtendedString (Rational)

let wall_test spec names_traces_results =
  let check (name, case, result) =
    let test () =
      let automaton = A.of_spec spec in
      Alcotest.(check bool) "same result" result
      @@ Option.is_some (A.accept_trace automaton Rational.zero case)
    in
    Alcotest.(test_case name `Quick) test
  in
  List.map check names_traces_results
;;

let logical_wall_test spec names_traces_results =
  let add_time (name, trace, result) =
    let trace =
      List.combine
        trace
        (List.init (List.length trace) (fun x -> Number.Rational.from_int (x + 1)))
    in
    name, trace, result
  in
  wall_test spec (List.map add_time names_traces_results)
;;

let true_false_cases trues falses =
  let trues = List.map (fun s -> s, A.trace_of_regexp s, true) trues in
  let falses = List.map (fun s -> s, A.trace_of_regexp s, false) falses in
  trues @ falses
;;

let rglwt spec l l' = logical_wall_test spec @@ true_false_cases l l'

let () =
  Alcotest.run
    "Simple Automata"
    [ "causality", rglwt [ Causality ("a", "b") ] [ "(ab)(ab)(ab)" ] [ "bbb"; "bababa" ]
    ; "precedence", rglwt [ Precedence ("a", "b") ] [ "a(ab)(ab)" ] [ "(ab)(ab)" ]
    ; "exclusion", rglwt [ Exclusion [ "a"; "b"; "c" ] ] [ "abc" ] [ "(ab)"; "(abc)" ]
    ; "periodic", rglwt [ Periodic ("o", "b", 3) ] [ "bb(bo)bb(bo)" ] [ "bbbbbb" ]
    ; "sample", rglwt [ Sample ("o", "i", "b") ] [ "ii(bo)"; "bbi(bo)" ] [ "bbo"; "(bo)" ]
      (*TODO: add more delay tests*)
    ; ( "delay-trivial"
      , rglwt [ Delay ("o", "i", (0, 0), None) ] [ "(oi)(oi)" ] [ "ooo"; "iiii" ] )
    ; ( "delay-simple"
      , rglwt [ Delay ("o", "i", (2, 2), None) ] [ "ii(oi)(oi)" ] [ "ooo"; "iiii" ] )
    ; ( "delay-undet"
      , rglwt
          [ Delay ("o", "i", (2, 4), None) ]
          [ "ii(oi)(oi)"; "ii(oi)i"; "iiii(oi)(oi)" ]
          [ "iiiii(oi)" ] )
    ; ( "delay-undet-zero"
      , rglwt
          [ Delay ("o", "i", (0, 2), None) ]
          [ "ii(oi)(oi)"; "(oi)(oi)" ]
          [ "iiiii"; "oooo" ] )
    ; ( "delay-sample"
      , rglwt
          [ Delay ("o", "i", (1, 2), Some "b") ]
          [ "ib(ib)(ob)"; "(ib)(ob)(ib)"; "iii"; "bbbb" ]
          [ "ooo" ] )
    ; ( "minus"
      , rglwt [ Minus ("m", "a", [ "b"; "c" ]) ] [ "(ma)"; "(ab)(ac)(abc)"; "bc" ] [ "a" ]
      )
    ; ( "union"
      , rglwt
          [ Union ("u", [ "a"; "b" ]) ]
          [ "(uab)(ua)(ub)" ]
          [ "u"; "ab"; "ba"; "(ab)" ] )
    ; "alternate", rglwt [ Alternate ("a", "b") ] [ "abab" ] [ "baba"; "aa" ]
    ; ( "fastest"
      , rglwt
          [ Fastest ("o", "a", "b") ]
          [ "(ao)b(bo)a"; "(abo)(abo)"; "(ao)(ao)(ao)" ]
          [ "aaaa"; "bbb"; "ooo" ] )
    ; ( "slowest"
      , rglwt
          [ Slowest ("o", "a", "b") ]
          [ "a(bo)b(ao)"; "(abo)(abo)"; "aaa(bo)(bo)(bo)"; "aaaa"; "bbb" ]
          [ "ooo" ] )
    ; ( "allow"
      , rglwt
          [ Allow ("f", "t", [ "a"; "b" ]) ]
          [ "fab(ab)t"; "(fa)(tb)" ]
          [ "aftb"; "b" ] )
    ; ( "allow-prec"
      , rglwt
          [ Allow ("f", "t", [ "a"; "b" ]); Precedence ("f", "a"); Precedence ("a", "t") ]
          [ "fat"; "fabt"; "fa(ft)at" ]
          [ "aftb"; "b"; "(fa)(tb)"; "faaat" ] )
    ; ( "forbid"
      , rglwt
          [ Forbid ("f", "t", [ "a" ]) ]
          [ ""; "f"; "t"; "a(ft)a"; "(fta)" ]
          [ "fat"; "ffatt" ] )
    ; ( "forbid-prec"
      , rglwt
          [ Forbid ("f", "t", [ "a" ]); Precedence ("f", "a"); Precedence ("a", "t") ]
          [ ""; "f" ]
          [ "fat" ] )
    ; ( "fl-sampled"
      , rglwt
          [ FirstSampled ("f", "a", "b"); LastSampled ("l", "a", "b") ]
          [ "(falb)(fa)(al)b" ]
          [ "ab"; "(lab)" ] )
    ; "subclock", rglwt [ Subclocking ("a", "b") ] [ "(ab)b" ] [ "a" ]
    ; ( "inter"
      , rglwt
          [ Intersection ("i", [ "a"; "b"; "c" ]) ]
          [ "(iabc)abc"; "(ab)" ]
          [ "(abc)"; "(iab)" ] )
    ]
;;
