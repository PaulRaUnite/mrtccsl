open Mrtccsl
open Prelude
open Rtccsl
open Number
module N = Integer
module A = Automata.Simple.MakeExtendedString (N)

let wall_test spec names_traces_results =
  let check (name, case, expected) =
    let test () =
      let automaton = A.of_spec spec in
      let trace_exist = Option.is_some (A.accept_trace automaton N.zero case) in
      Alcotest.(check bool) "same result" expected trace_exist
    in
    Alcotest.(test_case name `Quick) test
  in
  List.map check names_traces_results
;;

let logical_wall_test spec names_traces_results =
  let add_time (name, trace, result) =
    let trace =
      List.combine trace (List.init (List.length trace) (fun x -> N.from_int (x + 1)))
    in
    name, trace, result
  in
  wall_test spec (List.map add_time names_traces_results)
;;

let rglwt spec t f =
  let map v = List.map (fun s -> s, A.trace_of_regexp s, v) in
  let true_false_cases trues falses =
    let trues = map true trues in
    let falses = map false falses in
    trues @ falses
  in
  logical_wall_test spec @@ true_false_cases t f
;;

(** Real-time wall test maps trace strings and timescale to Alcotest cases. *)
let rtwt spec t f =
  let map v = List.map (fun (s, time) -> s, List.combine (A.trace_of_regexp s) time, v) in
  let cases = map true t @ map false f in
  wall_test spec cases
;;

let () =
  Alcotest.run
    "Simple Automata"
    [ ( "causality"
      , rglwt
          [ Causality { cause = "a"; effect = "b" } ]
          [ "(ab)(ab)(ab)" ]
          [ "bbb"; "bababa" ] )
    ; ( "precedence"
      , rglwt [ Precedence { cause = "a"; effect = "b" } ] [ "a(ab)(ab)" ] [ "(ab)(ab)" ]
      )
    ; "exclusion", rglwt [ Exclusion [ "a"; "b"; "c" ] ] [ "abc" ] [ "(ab)"; "(abc)" ]
    ; ( "periodic"
      , rglwt
          [ Periodic { out = "o"; base = "b"; period = 3 } ]
          [ "bb(bo)bb(bo)" ]
          [ "bbbbbb" ] )
    ; ( "sample"
      , rglwt
          [ Sample { out = "o"; arg = "i"; base = "b" } ]
          [ "ii(bo)"; "bbi(bo)" ]
          [ "bbo"; "(bo)" ] )
    ; ( "delay-trivial"
      , rglwt
          [ Delay { out = "o"; arg = "i"; delay = 0, 0; base = None } ]
          [ "(oi)(oi)" ]
          [ "ooo"; "iiii" ] )
    ; ( "delay-simple"
      , rglwt
          [ Delay { out = "o"; arg = "i"; delay = 2, 2; base = None } ]
          [ "ii(oi)(oi)" ]
          [ "ooo"; "iiii"; "iii(oi)(oi)"; "(oi)(oi)" ] )
    ; ( "delay-undet"
      , rglwt
          [ Delay { out = "o"; arg = "i"; delay = 2, 4; base = None } ]
          [ "ii(oi)(oi)"; "ii(oi)i"; "iiii(oi)(oi)" ]
          [ "iiiii(oi)" ] )
    ; ( "delay-undet-zero"
      , rglwt
          [ Delay { out = "o"; arg = "i"; delay = 0, 2; base = None } ]
          [ "ii(oi)(oi)"; "(oi)(oi)"; "(oi)ii(oi)" ]
          [ "iiiii"; "oooo" ] )
    ; ( "delay-sample"
      , rglwt
          [ Delay { out = "o"; arg = "i"; delay = 1, 2; base = Some "b" } ]
          [ "ib(ib)(ob)"; "(ib)(ob)(ib)b(ob)"; "iii"; "bbbb"; "(ib)b(ob)" ]
          [ "ooo"; "(ib)bbb(ob)" ] )
    ; ( "minus"
      , rglwt
          [ Minus { out = "m"; arg = "a"; except = [ "b"; "c" ] } ]
          [ "(ma)"; "(ab)(ac)(abc)"; "bc" ]
          [ "a" ] )
    ; ( "union"
      , rglwt
          [ Union { out = "u"; args = [ "a"; "b" ] } ]
          [ "(uab)(ua)(ub)" ]
          [ "u"; "ab"; "ba"; "(ab)" ] )
    ; ( "alternate"
      , rglwt [ Alternate { first = "a"; second = "b" } ] [ "abab" ] [ "baba"; "aa" ] )
    ; ( "fastest"
      , rglwt
          [ Fastest { out = "o"; left = "a"; right = "b" } ]
          [ "(ao)b(bo)a"; "(abo)(abo)"; "(ao)(ao)(ao)" ]
          [ "aaaa"; "bbb"; "ooo" ] )
    ; ( "slowest"
      , rglwt
          [ Slowest { out = "o"; left = "a"; right = "b" } ]
          [ "a(bo)b(ao)"; "(abo)(abo)"; "aaa(bo)(bo)(bo)"; "aaaa"; "bbb" ]
          [ "ooo" ] )
    ; ( "allow"
      , rglwt
          [ Allow { from = "f"; until = "t"; args = [ "a"; "b" ] } ]
          [ "fab(ab)t"; "(fa)(tb)" ]
          [ "aftb"; "b" ] )
    ; ( "allow-prec"
      , rglwt
          [ Allow { from = "f"; until = "t"; args = [ "a"; "b" ] }
          ; Precedence { cause = "f"; effect = "a" }
          ; Precedence { cause = "a"; effect = "t" }
          ]
          [ "fat"; "fabt"; "fa(ft)at" ]
          [ "aftb"; "b"; "(fa)(tb)"; "faaat" ] )
    ; ( "forbid"
      , rglwt
          [ Forbid { from = "f"; until = "t"; args = [ "a" ] } ]
          [ ""; "f"; "t"; "a(ft)a"; "(fta)" ]
          [ "fat"; "ffatt" ] )
    ; ( "forbid-prec"
      , rglwt
          [ Forbid { from = "f"; until = "t"; args = [ "a" ] }
          ; Precedence { cause = "f"; effect = "a" }
          ; Precedence { cause = "a"; effect = "t" }
          ]
          [ ""; "f" ]
          [ "fat" ] )
    ; ( "fl-sampled"
      , rglwt
          [ FirstSampled { out = "f"; arg = "a"; base = "b" }
          ; LastSampled { out = "l"; arg = "a"; base = "b" }
          ]
          [ "(falb)(fa)(al)b" ]
          [ "ab"; "(lab)" ] )
    ; "subclock", rglwt [ Subclocking { sub = "a"; super = "b" } ] [ "(ab)b" ] [ "a" ]
    ; ( "inter"
      , rglwt
          [ Intersection { out = "i"; args = [ "a"; "b"; "c" ] } ]
          [ "(iabc)abc"; "(ab)" ]
          [ "(abc)"; "(iab)" ] )
    ; ( "rt-delay"
      , rtwt
          [ RTdelay { arg = "i"; out = "o"; delay = 1, 3 } ]
          [ "io", [ 4; 6 ]; "i(io)o", [ 2; 3; 6 ]; "i", [ 500 ] ]
          [ "ioo", [ 1; 2; 3 ]; "io", [ 3; 10 ] ] )
    ; ( "cum-period"
      , rtwt
          [ CumulPeriodic { out = "o"; period = 4; error = -1, 1; offset = 2 } ]
          [ "ooo", [ 2; 6; 10 ]; "ooo", [ 1; 4; 7 ] ]
          [ "o", [ 4 ]; "ooo", [ 1; 5; 11 ] ] )
    ; ( "abs-period"
      , rtwt
          [ AbsPeriodic { out = "o"; period = 4; error = -1, 1; offset = 2 } ]
          [ "ooo", [ 2; 6; 10 ]; "ooo", [ 1; 5; 11 ] ]
          [ "o", [ 4 ]; "ooo", [ 1; 4; 7 ] ] )
    ; ( "sporadic"
      , rtwt
          [ Sporadic { out = "a"; at_least = 2; strict = false } ]
          [ "aaa", [ 1; 3; 5 ]; "aaa", [ 5; 10; 1000 ] ]
          [ "aa", [ 2; 3 ] ] )
    ]
;;
