open Mrtccsl
open Prelude
module A = Automata.Simple.MakeExtendedString (Number.Rational)
open Number.Rational

let step = of_int 1 / of_int 10

let random_strat =
  A.Strategy.random_label
    (A.Strategy.random_leap (of_int 1) (round_up step) (round_down step) random)
;;

let fast_strat = A.Strategy.random_label @@ A.Strategy.fast (of_int 2) (round_down step)
let one = of_int 1
let two = of_int 2
let hundred = of_int 100
let half = of_int 1 / of_int 2

let () =
  let _ = Random.init 127649812489 in
  let ie = of_int 1 in
  let rr = of_int 30 / of_int 60 in
  let inspiration_duration = one / rr / (one + ie) in
  let trigger_delay = of_int 7 / of_int 10 in
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
    (* [Rtccsl.Allow ("from", "to", ["a"])] *)
    (* [Rtccsl.FirstSampled("o", "a", "b"); Rtccsl.Sample ("s", "a", "b")] *)
    Rtccsl.
      [ RTdelay
          { arg = "inspiration"
          ; out = "expiration"
          ; delay = TimeConst inspiration_duration, TimeConst inspiration_duration
          }
      ; Precedence { cause = "trigger.start"; conseq = "trigger.finish" }
      ; Allow
          { from = "trigger.start"; until = "trigger.finish"; args = [ "sensor.inhale" ] }
      ; RTdelay
          { arg = "expiration"
          ; out = "trigger.start"
          ; delay = TimeConst trigger_delay, TimeConst trigger_delay
          }
      ; RTdelay
          { arg = "inspiration"
          ; out = "trigger.finish"
          ; delay = TimeConst (one / rr), TimeConst (one / rr)
          }
      ; Delay
          { out = "next inspiration"
          ; arg = "inspiration"
          ; delay = IntConst 1, IntConst 1
          ; base = None
          }
      ; Sample { out = "s"; arg = "sensor.inhale"; base = "trigger.finish" }
      ; Minus { out = "-"; arg = "trigger.finish"; except = [ "s" ] }
      ; Union { out = "cond"; args = [ "sensor.inhale"; "-" ] }
      ; FirstSampled { out = "first"; arg = "cond"; base = "trigger.finish" }
      ; RTdelay
          { arg = "first"
          ; out = "next inspiration"
          ; delay = TimeConst (one / hundred), TimeConst (two / hundred)
          }
      ]
  in
  let a = A.of_spec spec in
  let trace = A.gen_trace fast_strat 20 a in
  let trace = A.skip_empty trace in
  let g, _, clocks = a in
  (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 2.0); *)
  let svgbob_str = A.trace_to_svgbob ~numbers:false (A.L.elements clocks) trace in
  print_endline svgbob_str
;;
