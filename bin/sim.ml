open Mrtccsl
open Prelude
module A = Automata.Simple.MakeExtendedString (Number.Rational)
open Number.Rational

let step = of_int 1 / of_int 10

let random_strat =
  A.Strategy.Solution.random_label
    (A.Strategy.Num.random_leap
       ~upper_bound:(of_int 1)
       ~ceil:(round_up step)
       ~floor:(round_down step)
       ~rand:random)
;;

let fast_strat =
  A.Strategy.Solution.random_label
  @@ A.Strategy.Num.fast ~upper_bound:(of_int 2) ~floor:(round_down step)
;;

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
  let inspiration_delay_var = "insp.del" in
  let trigger_delay_var = "trigger_del" in
  let inspiration_trigger_delay_name = "inspiration_trigger_delay" in
  let first_to_next = "first_to_second" in
  let constraints =
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
      [ RTdelay { arg = "inspiration"; out = "expiration"; delay = inspiration_delay_var }
      ; Precedence { cause = "trigger.start"; conseq = "trigger.finish" }
      ; Allow
          { from = "trigger.start"; until = "trigger.finish"; args = [ "sensor.inhale" ] }
      ; RTdelay { arg = "expiration"; out = "trigger.start"; delay = trigger_delay_var }
      ; RTdelay
          { arg = "inspiration"
          ; out = "trigger.finish"
          ; delay = inspiration_trigger_delay_name
          }
      ; Delay
          { out = "next inspiration"
          ; arg = "inspiration"
          ; delay = Const 1, Const 1
          ; base = None
          }
      ; Sample { out = "s"; arg = "sensor.inhale"; base = "trigger.finish" }
      ; Minus { out = "-"; arg = "trigger.finish"; except = [ "s" ] }
      ; Union { out = "cond"; args = [ "sensor.inhale"; "-" ] }
      ; FirstSampled { out = "first"; arg = "cond"; base = "trigger.finish" }
      ; RTdelay { arg = "first"; out = "next inspiration"; delay = first_to_next }
      ]
  in
  let var_relations =
    Rtccsl.
      [ TimeVarRelation (inspiration_delay_var, Eq, Const inspiration_duration)
      ; TimeVarRelation (trigger_delay_var, Eq, Const trigger_delay)
      ; TimeVarRelation (inspiration_trigger_delay_name, Eq, Const (one / rr))
      ; TimeVarRelation (first_to_next, MoreEq, Const (one / hundred))
      ; TimeVarRelation (first_to_next, LessEq, Const (two / hundred))
      ]
  in
  let env = A.of_spec { constraints; var_relations } in
  let trace = A.gen_trace A.Strategy.Var.none fast_strat env in
  let trace = A.skip_empty trace in
  let _, (_, _, clocks) = env in
  (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 2.0); *)
  let svgbob_str = A.trace_to_svgbob ~numbers:false (A.L.elements clocks) trace in
  print_endline svgbob_str
;;
