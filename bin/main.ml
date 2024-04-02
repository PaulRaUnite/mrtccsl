open Prelude


module A =
  Automata.AddSVGBobSerialize (Automata.MakeSimple (Clock.String) (Number.Float)) (Clock.String) (Number.Float)

let step = 0.1

let round_up x y =
  let v = x +. step in
  if v > y then (x +. y) /. 2. else v
;;

let round_down x y =
  let v = y -. step in
  if v < x then (x +. y) /. 2. else v
;;

let random_float x y = if Float.equal x y then x else x +. Random.float (y -. x)

let random_strat =
  A.Strategy.random_label
    (A.Strategy.random_leap A.I.(0.0 =-= 1.0) round_up round_down random_float)
;;

let () =
  let spec = [ Rtccsl.Precedence( "a", "b") ] in
  let a = A.of_spec spec in
  let trace = A.run random_strat a 10 in
  let _, _, clocks = a in
  let svgbob_str = A.trace_to_svgbob clocks trace in
  print_endline svgbob_str
;;
