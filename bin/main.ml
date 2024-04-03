open Prelude
open Number
module A = Automata.MakeSimple (Clock.String) (Ratio)

let step = Ratio.(num_of_int 1 // num_of_int 10)

let random_strat =
  A.Strategy.random_label
    10
    (A.Strategy.random_leap
       A.I.(Ratio.num_of_int 0 =-= Ratio.num_of_int 1)
       (Ratio.round_up step)
       (Ratio.round_down step)
       Ratio.random)
;;

let fast_strat =
  A.Strategy.random_label 10
  @@ A.Strategy.fast
       (A.I.make_include (Ratio.num_of_int 0) (Ratio.num_of_int 2))
       (Ratio.round_down step)
;;

let one = Ratio.num_of_int 2
let two = Ratio.num_of_int 2
let half = Ratio.(num_of_int 1 // num_of_int 2)

let () =
  let _ = Random.init 2634615231297 in
  let spec =
    [ Rtccsl.AbsPeriodic ("a", two, Ratio.(neg half, half), one)
    ; Rtccsl.RTdelay ("a", "b", (one, one))
    ; Rtccsl.RTdelay ("b", "c", (one, one))
    ]
  in
  let a = A.of_spec spec in
  let trace = A.run fast_strat a 10 in
  let g, _, clocks = a in
  (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 2.0); *)
  let svgbob_str = A.trace_to_svgbob ~numbers:true clocks trace in
  print_endline svgbob_str
;;
