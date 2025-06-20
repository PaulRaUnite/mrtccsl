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
    name, trace |> List.to_seq |> A.Trace.of_seq, result
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
  let map v =
    List.map (fun (s, time) ->
      s, List.combine (A.trace_of_regexp s) time |> List.to_seq |> A.Trace.of_seq, v)
  in
  let cases = map true t @ map false f in
  wall_test spec cases
;;

let () =
  Alcotest.run
    "Simple Automata"
    [ ( "causality"
      , rglwt
          (constraints_only [ Causality { cause = "a"; conseq = "b" } ])
          [ "(ab)(ab)(ab)" ]
          [ "bbb"; "bababa" ] )
    ; ( "precedence"
      , rglwt
          (constraints_only [ Precedence { cause = "a"; conseq = "b" } ])
          [ "a(ab)(ab)" ]
          [ "(ab)(ab)" ] )
    ; ( "exclusion"
      , rglwt
          (constraints_only [ Exclusion [ "a"; "b"; "c" ] ])
          [ "abc" ]
          [ "(ab)"; "(abc)" ] )
    ; ( "periodic"
      , rglwt
          (constraints_only [ Periodic { out = "o"; base = "b"; period = const 3 } ])
          [ "bb(bo)bb(bo)" ]
          [ "bbbbbb" ] )
    ; ( "sample"
      , rglwt
          (constraints_only [ Sample { out = "o"; arg = "i"; base = "b" } ])
          [ "ii(bo)"; "bbi(bo)" ]
          [ "bbo"; "(bo)" ] )
    ; ( "delay-trivial"
      , rglwt
          (constraints_only
             [ Delay { out = "o"; arg = "i"; delay = const 0, const 0; base = None } ])
          [ "(oi)(oi)" ]
          [ "ooo"; "iiii" ] )
    ; ( "delay-simple"
      , rglwt
          (constraints_only
             [ Delay { out = "o"; arg = "i"; delay = const 2, const 2; base = None } ])
          [ "ii(oi)(oi)" ]
          [ "ooo"; "iiii"; "iii(oi)(oi)"; "(oi)(oi)" ] )
    ; ( "delay-undet"
      , rglwt
          (constraints_only
             [ Delay { out = "o"; arg = "i"; delay = const 2, const 4; base = None } ])
          [ "ii(oi)(oi)"; "ii(oi)i"; "iiii(oi)(oi)" ]
          [ "iiiii(oi)" ] )
    ; ( "delay-undet-zero"
      , rglwt
          (constraints_only
             [ Delay { out = "o"; arg = "i"; delay = const 0, const 2; base = None } ])
          [ "ii(oi)(oi)"; "(oi)(oi)"; "(oi)ii(oi)" ]
          [ "iiiii"; "oooo" ] )
    ; ( "delay-sample"
      , rglwt
          (constraints_only
             [ Delay { out = "o"; arg = "i"; delay = const 1, const 2; base = Some "b" } ])
          [ "ib(ib)(ob)"; "(ib)(ob)(ib)b(ob)"; "iii"; "bbbb"; "(ib)b(ob)" ]
          [ "ooo"; "(ib)bbb(ob)" ] )
    ; ( "minus"
      , rglwt
          (constraints_only [ Minus { out = "m"; arg = "a"; except = [ "b"; "c" ] } ])
          [ "(ma)"; "(ab)(ac)(abc)"; "bc" ]
          [ "a" ] )
    ; ( "union"
      , rglwt
          (constraints_only [ Union { out = "u"; args = [ "a"; "b" ] } ])
          [ "(uab)(ua)(ub)" ]
          [ "u"; "ab"; "ba"; "(ab)" ] )
    ; ( "alternate"
      , rglwt
          (constraints_only [ Alternate { first = "a"; second = "b" } ])
          [ "abab" ]
          [ "baba"; "aa" ] )
    ; ( "fastest"
      , rglwt
          (constraints_only [ Fastest { out = "o"; left = "a"; right = "b" } ])
          [ "(ao)b(bo)a"; "(abo)(abo)"; "(ao)(ao)(ao)" ]
          [ "aaaa"; "bbb"; "ooo" ] )
    ; ( "slowest"
      , rglwt
          (constraints_only [ Slowest { out = "o"; left = "a"; right = "b" } ])
          [ "a(bo)b(ao)"; "(abo)(abo)"; "aaa(bo)(bo)(bo)"; "aaaa"; "bbb" ]
          [ "ooo" ] )
    ; ( "allow"
      , rglwt
          (constraints_only [ Allow { from = "f"; until = "t"; args = [ "a"; "b" ] } ])
          [ "fab(ab)t"; "(fa)(tb)" ]
          [ "aftb"; "b" ] )
    ; ( "allow-prec"
      , rglwt
          (constraints_only
             [ Allow { from = "f"; until = "t"; args = [ "a"; "b" ] }
             ; Precedence { cause = "f"; conseq = "a" }
             ; Precedence { cause = "a"; conseq = "t" }
             ])
          [ "fat"; "fabt"; "fa(ft)at" ]
          [ "aftb"; "b"; "(fa)(tb)"; "faaat" ] )
    ; ( "forbid"
      , rglwt
          (constraints_only [ Forbid { from = "f"; until = "t"; args = [ "a" ] } ])
          [ ""; "f"; "t"; "a(ft)a"; "(fta)" ]
          [ "fat"; "ffatt" ] )
    ; ( "forbid-prec"
      , rglwt
          (constraints_only
             [ Forbid { from = "f"; until = "t"; args = [ "a" ] }
             ; Precedence { cause = "f"; conseq = "a" }
             ; Precedence { cause = "a"; conseq = "t" }
             ])
          [ ""; "f" ]
          [ "fat" ] )
    ; ( "fl-sampled"
      , rglwt
          (constraints_only
             [ FirstSampled { out = "f"; arg = "a"; base = "b" }
             ; LastSampled { out = "l"; arg = "a"; base = "b" }
             ])
          [ "(falb)(fa)(al)b" ]
          [ "ab"; "(lab)" ] )
    ; ( "subclock"
      , rglwt
          (constraints_only [ Subclocking { sub = "a"; super = "b" } ])
          [ "(ab)b" ]
          [ "a" ] )
    ; ( "inter"
      , rglwt
          (constraints_only [ Intersection { out = "i"; args = [ "a"; "b"; "c" ] } ])
          [ "(iabc)abc"; "(ab)" ]
          [ "(abc)"; "(iab)" ] )
    ; ( "rt-delay"
      , rtwt
          { constraints = [ RTdelay { arg = "i"; out = "o"; delay = "t" } ]
          ; var_relations =
              [ TimeVarRelation ("t", LessEq, Const 3)
              ; TimeVarRelation ("t", MoreEq, Const 1)
              ]
          }
          [ "io", [ 4; 6 ]; "i(io)o", [ 2; 3; 6 ]; "i", [ 500 ] ]
          [ "ioo", [ 1; 2; 3 ]; "io", [ 3; 10 ] ] )
    ; ( "cum-period"
      , rtwt
          { constraints = [ CumulPeriodic { out = "o"; period = "p"; offset = Const 2 } ]
          ; var_relations =
              [ TimeVarRelation ("p", LessEq, Const 5)
              ; TimeVarRelation ("p", MoreEq, Const 3)
              ]
          }
          [ "ooo", [ 2; 6; 10 ]; "ooo", [ 2; 5; 8 ] ]
          [ "o", [ 4 ]; "o", [ 1 ]; "oo", [ 2; 11 ] ] )
    ; ( "abs-period"
      , rtwt
          { constraints =
              [ AbsPeriodic { out = "o"; period = Const 4; error = "e"; offset = Const 2 }
              ]
          ; var_relations =
              [ TimeVarRelation ("e", LessEq, Const 1)
              ; TimeVarRelation ("e", MoreEq, Const ~-1)
              ]
          }
          [ "ooo", [ 2; 6; 10 ]; "ooo", [ 1; 5; 11 ] ]
          [ "o", [ 4 ]; "ooo", [ 1; 4; 7 ] ] )
    ; ( "sporadic"
      , rtwt
          (constraints_only
             [ Sporadic { out = "a"; at_least = Const 2; strict = false } ])
          [ "aaa", [ 1; 3; 5 ]; "aaa", [ 5; 10; 1000 ] ]
          [ "aa", [ 2; 3 ] ] )
    ]
;;
