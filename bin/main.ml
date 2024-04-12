open Prelude
module A = Automata.Simple.Make (Clock.String) (Number.Rational)
open Number.Rational

let step = num_of_int 1 // num_of_int 10

let random_strat =
  A.Strategy.random_label
    10
    (A.Strategy.random_leap
       A.I.(num_of_int 0 =-= num_of_int 1)
       (round_up step)
       (round_down step)
       random)
;;

let fast_strat =
  A.Strategy.random_label 10
  @@ A.Strategy.fast (A.I.make_include (num_of_int 0) (num_of_int 2)) (round_down step)
;;

let one = num_of_int 1
let two = num_of_int 2
let half = Ratio.(num_of_int 1 // num_of_int 2)

let () =
  let _ = Random.init 872478216 in
  let spec =
    (* [
       Rtccsl.AbsPeriodic ("a", two, Ratio.(neg half, half), one)
    ; Rtccsl.RTdelay ("a", "b", (one, one))
    ; Rtccsl.RTdelay ("b", "c", (one, one))
    ] *)
    (* [Rtccsl.Periodic ("o", "in", 4)] *)
    (* [Rtccsl.Delay ("o", "i", (0,0), Some "b")] *)
    (* [Rtccsl.Alternate ("a", "b")] *)
    (* [Rtccsl.AbsPeriodic ("a", two, Ratio.(neg half, half), one); Rtccsl.Minus("o", "a", ["b"])] *)
    (* [Rtccsl.Fastest("o", "a", "b")] *)
    [Rtccsl.Allow ("from", "to", ["a"])]
  in
  let a = A.of_spec spec in
  let trace = A.run fast_strat a 20 in
  let trace = A.skip_empty trace in
  let g, _, clocks = a in
  (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 2.0); *)
  let svgbob_str = A.trace_to_svgbob ~numbers:false clocks trace in
  print_endline svgbob_str
;;
