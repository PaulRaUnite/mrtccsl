open Prelude
open Rtccsl
open Number
module A = Automata.Simple.Make (Clock.String) (Rational)

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

let logical_wall_test spec traces results =
  let add_time trace =
    List.combine
      trace
      (List.init (List.length trace) (fun x -> Number.Rational.from_int (x + 1)))
  in
  let traces = List.map add_time traces in
  wall_test spec traces results
;;

let trace_of_string l =
  let to_clock_seq (c, s) =
    Seq.map (fun char -> if char = 'x' then Some c else None) (String.to_seq s)
  in
  let clock_traces = List.map to_clock_seq l in
  let clocks_trace = Seq.zip_list clock_traces in
  List.of_seq
  @@ Seq.map
       (fun cs ->
         let clocks, _ = List.flatten_opt cs in
         A.L.of_list clocks)
       clocks_trace
;;

let () =
  Alcotest.run
    "Simple Automata"
    [ ( "causality"
      , logical_wall_test
          [ Causality ("a", "b") ]
          [ trace_of_string [ "a", "xxxxxxxxx"; "b", "xxx    xx" ] ]
          [ true ] )
    ]
;;
