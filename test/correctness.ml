open Mrtccsl
open Prelude
open Language
open Cstr
open Language.Specification
open Builder

module type BackendS = sig
  val test_name : string

  module N : sig
    type t

    val zero : t
    val of_int : int -> t
  end

  module Trace : sig
    type t

    module String : sig
      val trace_of_regexp : string -> N.t Seq.t -> t
    end
  end

  module Backend : sig
    type sim

    val of_spec
      :  ?debug:bool
      -> (string, string, string, string, string, N.t) Specification.t
      -> sim

    val accept_trace : sim -> Trace.t -> bool
  end
end

module Make (B : BackendS) = struct
  open B

  let wall_test spec names_traces_results =
    let check (name, case, expected) =
      let test () =
        let automaton =
          Backend.of_spec
            (Specification.map Fun.id Fun.id Fun.id Fun.id Fun.id N.of_int spec)
        in
        let trace_accepted = Backend.accept_trace automaton case in
        Alcotest.(check bool) "same result" expected trace_accepted
      in
      Alcotest.(test_case name `Quick) test
    in
    List.map check names_traces_results
  ;;

  let order_test spec true_cases false_cases =
    let timestamps = Seq.map N.of_int (Seq.ints 0) in
    let map v cases =
      let tests =
        List.map
          (fun labels_str ->
             let trace = Trace.String.trace_of_regexp labels_str timestamps in
             labels_str, trace, v)
          cases
      in
      if v
      then ("empty", Trace.String.trace_of_regexp "()" timestamps, true) :: tests
      else tests
    in
    let trues = map true true_cases in
    let falses = map false false_cases in
    let all_cases = trues @ falses in
    wall_test spec all_cases
  ;;

  (** Real-time wall test maps trace strings and timescale to Alcotest cases. *)
  let rtime_test spec t f =
    let map v =
      List.map (fun (s, time) ->
        s, Trace.String.trace_of_regexp s (List.to_seq time |> Seq.map N.of_int), v)
    in
    let cases = map true t @ map false f in
    wall_test spec cases
  ;;

  let cco = clock_constraints_only

  let () =
    Alcotest.run
      B.test_name
      [ ( "causality"
        , order_test
            (cco [ Causality { cause = "a"; conseq = "b" } ])
            [ "(ab)(ab)(ab)"; "a(ab)b"; "aabb" ]
            [ "bbb"; "bababa"; "aaabbbb" ] )
      ; ( "precedence"
        , order_test
            (cco [ Precedence { cause = "a"; conseq = "b" } ])
            [ "a(ab)(ab)"; "aaabbb" ]
            [ "(ab)(ab)"; "aabbb"; "bbb" ] )
      ; ( "exclusion"
        , order_test
            (cco [ Exclusion { args = [ "a"; "b"; "c" ]; choice = None } ])
            [ "abc" ]
            [ "(ab)"; "(abc)" ] )
      ; ( "coincidence"
        , order_test
            (cco [ Coincidence [ "a"; "b"; "c" ] ])
            [ "(abc)(abc)(cab)" ]
            [ "a"; "b"; "c"; "(bc)"; "(abc)a" ] )
      ; ( "periodic[p=3;offset=0]"
        , order_test
            (cco
               [ Periodic
                   { out = "o"
                   ; base = "b"
                   ; period = 3
                   ; error = const 0
                   ; offset = const 0
                   }
               ])
            [ "(bo)bb(bo)bb(bo)" ]
            [ "bbbbbb"; "(bo)bbbbbb(bo)" ] )
      ; ( "periodic[p=3,offset=2]"
        , order_test
            (cco
               [ Periodic
                   { out = "o"
                   ; base = "b"
                   ; period = 3
                   ; error = const 0
                   ; offset = const 2
                   }
               ])
            [ "bb(bo)bb(bo)"; "bb" ]
            [ "bbbbbb"; "(bo)bb"; "b(bo)" ] )
      ; ( "periodic[p=3,offset=2,error=+-1]"
        , order_test
            (of_decl (fun b ->
               logical b
               @@ Periodic
                    { out = "o"
                    ; base = "b"
                    ; period = 3
                    ; error = var "e"
                    ; offset = const 2
                    };
               integer b @@ NumRelation ("e", `LessEq, const 1);
               integer b @@ NumRelation ("e", `MoreEq, const (-1))))
            [ "bb(bo)bb(bo)"; "bb"; "bb(bo)b(bo)bbb(bo)" ]
            [ "bbbbbbbbb"; "bb(bo)(bo)"; "bb(bo)bbbbb(bo)" ] )
      ; ( "sample"
        , order_test
            (cco [ Sample { out = "o"; arg = "i"; base = "b" } ])
            [ "ii(bo)"; "bbi(bo)" ]
            [ "bbo"; "(bo)"; "biib" ] )
      ; ( "delay-trivial"
        , order_test
            (cco [ Delay { out = "o"; arg = "i"; delay = const 0; base = "i" } ])
            [ "(oi)(oi)" ]
            [ "ooo"; "iiii" ] )
      ; ( "delay-simple"
        , order_test
            (cco [ Delay { out = "o"; arg = "i"; delay = const 2; base = "i" } ])
            [ "ii(oi)(oi)" ]
            [ "ooo"; "iiii"; "iii(oi)(oi)"; "(oi)(oi)" ] )
      ; ( "delay-undet"
        , order_test
            (of_decl (fun b ->
               logical b
               @@ Delay { out = "o"; arg = "i"; delay = var "duration"; base = "i" };
               integer b @@ NumRelation ("duration", `LessEq, const 4);
               integer b @@ NumRelation ("duration", `MoreEq, const 2)))
            [ "ii(oi)(oi)"; "ii(oi)i"; "iiii(oi)(oi)" ]
            [ "iiiii(oi)" ] )
      ; ( "delay-undet-zero"
        , order_test
            (of_decl (fun b ->
               logical b
               @@ Delay { out = "o"; arg = "i"; delay = var "duration"; base = "i" };
               integer b @@ NumRelation ("duration", `LessEq, const 2);
               integer b @@ NumRelation ("duration", `MoreEq, const 0)))
            [ "ii(oi)(oi)"; "(oi)(oi)"; "(oi)ii(oi)" ]
            [ "iiiii"; "oooo" ] )
      ; ( "delay-sample"
        , order_test
            (of_decl (fun b ->
               logical b
               @@ Delay { out = "o"; arg = "i"; delay = var "duration"; base = "b" };
               integer b @@ NumRelation ("duration", `LessEq, const 2);
               integer b @@ NumRelation ("duration", `MoreEq, const 1)))
            [ "ib(ib)(ob)"; "(ib)(ob)(ib)b(ob)"; "iii"; "bbbb"; "(ib)b(ob)" ]
            [ "ooo"; "(ib)bbb(ob)" ] )
      ; ( "minus"
        , order_test
            (cco [ Minus { out = "m"; arg = "a"; except = [ "b"; "c" ] } ])
            [ "(ma)"; "(ab)(ac)(abc)"; "bc" ]
            [ "a"; "(mabc)" ] )
      ; ( "union"
        , order_test
            (cco [ Union { out = "u"; args = [ "a"; "b" ] } ])
            [ "(uab)(ua)(ub)" ]
            [ "u"; "ab"; "ba"; "(ab)" ] )
      ; ( "disj-union"
        , order_test
            (cco [ DisjunctiveUnion { out = "u"; args = [ "a"; "b" ]; choice = None } ])
            [ "(au)"; "(bu)" ]
            [ "a"; "b"; "(uab)"; "(ab)"; "u" ] )
      ; ( "alternate-strict"
        , order_test
            (cco [ Alternate { first = "a"; second = "b"; strict = true } ])
            [ "abab" ]
            [ "baba"; "aa"; "a(ab)b" ] )
      ; ( "alternate-nonstrict"
        , order_test
            (cco [ Alternate { first = "a"; second = "b"; strict = false } ])
            [ "abab"; "a(ab)b" ]
            [ "baba"; "aa" ] )
      ; ( "fastest"
        , order_test
            (cco [ Fastest { out = "o"; args = [ "a"; "b" ] } ])
            [ "(ao)b(bo)a"; "(abo)(abo)"; "(ao)(ao)(ao)bbb" ]
            [ "aaaa"; "bbb"; "ooo"; "(ao)(bo)"; "(ao)a" ] )
      ; ( "slowest"
        , order_test
            (cco [ Slowest { out = "o"; args = [ "a"; "b" ] } ])
            [ "a(bo)b(ao)"; "(abo)(abo)"; "aaa(bo)(bo)(bo)"; "aaaa"; "bbb" ]
            [ "ooo"; "ab"; "bo" ] )
      ; ( "allow[f,t)"
        , order_test
            (cco [ Allow { left = "f"; right = "t"; args = [ "a"; "b" ] } ])
            [ "fab(ab)t"; "(fa)t" ]
            [ "aftb"; "b" ] )
        (* ; ( "allow(f,t]"
      , rglwt
          (cco
             [ Allow
                 { left = "f"
                 ; right = "t"
                 ; left_strict = true
                 ; right_strict = false
                 ; args = [ "a"; "b" ]
                 }
             ])
          [ "fabt"; "f(abt)" ]
          [ "aft"; "ftb"; "(fab)t" ] ) *)
      ; ( "allow-prec"
        , order_test
            (cco
               [ Allow { left = "f"; right = "t"; args = [ "a"; "b" ] }
               ; Precedence { cause = "f"; conseq = "a" }
               ; Precedence { cause = "a"; conseq = "t" }
               ])
            [ "fat"; "fabt"; "fafatt" ]
            [ "aftb"; "b"; "(fa)tb"; "faaat" ] )
      ; ( "forbid[f,t)"
        , order_test
            (cco [ Forbid { left = "f"; right = "t"; args = [ "a" ] } ])
            [ "f"; "afta"; "f(ta)"; "(ft)" ]
            [ "fat"; "ffatt"; "a(fa)"; "t" ] )
      ; ( "forbid-prec"
        , order_test
            (cco
               [ Forbid { left = "f"; right = "t"; args = [ "a" ] }
               ; Precedence { cause = "f"; conseq = "a" }
               ; Precedence { cause = "a"; conseq = "t" }
               ])
            [ ""; "f" ]
            [ "fat" ] )
      ; ( "fl-sampled"
        , order_test
            (cco
               [ FirstSampled { out = "f"; arg = "a"; base = "b" }
               ; LastSampled { out = "l"; arg = "a"; base = "b" }
               ])
            [ "(falb)(fa)(al)b" ]
            [ "ab"; "(lab)" ] )
      ; ( "subclocking"
        , order_test
            (cco [ Subclocking { sub = "a"; super = "b"; choice = None } ])
            [ "(ab)b" ]
            [ "a" ] )
      ; ( "intersection"
        , order_test
            (cco [ Intersection { out = "i"; args = [ "a"; "b"; "c" ] } ])
            [ "(iabc)abc"; "(ab)" ]
            [ "(abc)"; "(iab)"; "i" ] )
      ; ( "rt-delay-const"
        , rtime_test
            (cco [ RTdelay { arg = "i"; out = "o"; delay = const 4 } ])
            [ "io", [ 4; 8 ]; "i(io)o", [ 2; 6; 10 ]; "i", [ 500 ] ]
            [ "io", [ 1; 2 ]; "io", [ 1; 10 ]; "o", [ 5 ] ] )
      ; ( "rt-delay"
        , rtime_test
            (of_decl (fun b ->
               logical b @@ RTdelay { arg = "i"; out = "o"; delay = var "t" };
               duration b @@ NumRelation ("t", `LessEq, Const 3);
               duration b @@ NumRelation ("t", `MoreEq, Const 1)))
            [ "io", [ 4; 6 ]; "i(io)o", [ 2; 3; 6 ]; "i", [ 500 ] ]
            [ "ioo", [ 1; 2; 3 ]; "io", [ 3; 10 ] ] )
      ; ( "cumul-period"
        , rtime_test
            (of_decl (fun b ->
               logical b
               @@ CumulPeriodic
                    { out = "o"; period = 4; error = var "e"; offset = const 2 };
               duration b @@ NumRelation ("e", `LessEq, Const 1);
               duration b @@ NumRelation ("e", `MoreEq, Const (-1))))
            [ "ooo", [ 2; 6; 10 ]; "ooo", [ 2; 5; 8 ] ]
            [ "o", [ 4 ]; "o", [ 1 ]; "oo", [ 2; 11 ] ] )
      ; ( "abs-period"
        , rtime_test
            (of_decl (fun b ->
               logical b
               @@ AbsPeriodic { out = "o"; period = 4; error = var "e"; offset = const 2 };
               duration b @@ NumRelation ("e", `LessEq, Const 1);
               duration b @@ NumRelation ("e", `MoreEq, Const (-1))))
            [ "ooo", [ 2; 6; 10 ]; "ooo", [ 2; 5; 11 ] ]
            [ "o", [ 4 ]; "ooo", [ 1; 4; 7 ] ] )
      ; ( "sporadic-nonstrict"
        , rtime_test
            (cco [ Sporadic { out = "a"; at_least = Const 2; strict = false } ])
            [ "aaa", [ 1; 3; 5 ] ]
            [ "aa", [ 2; 3 ] ] )
      ; ( "sporadic-strict"
        , rtime_test
            (cco [ Sporadic { out = "a"; at_least = Const 2; strict = true } ])
            [ "aaa", [ 1; 4; 7 ] ]
            [ "aaa", [ 1; 3; 5 ] ] )
      ; ( "sporadic-strict-undet"
        , rtime_test
            (of_decl (fun b ->
               logical b @@ Sporadic { out = "a"; at_least = var "d"; strict = true };
               duration b @@ NumRelation ("d", `MoreEq, const 2);
               duration b @@ NumRelation ("d", `LessEq, const 4)))
            [ "aaa", [ 1; 4; 7 ] ]
            [ "aaa", [ 1; 3; 5 ] ] )
      ]
  ;;
end
