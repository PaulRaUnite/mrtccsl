include Stdlib.Float
include Interface.ExpOrder.Make (Stdlib.Float)

let ( + ) = add
let ( - ) = sub
let ( * ) = mul
let ( / ) = div
let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_float
let t_of_sexp = Sexplib0.Sexp_conv.float_of_sexp
let t_to_string x = Printf.sprintf "%f" x

let round_up step x y =
  let v = x +. step in
  let r = if v >= y then (x +. y) /. 2. else v in
  (* let _ = Printf.printf "%f\n" r in *)
  r
;;

let round_down step x y =
  let v = y -. step in
  (* let _ = Printf.printf "v: %f %f %f\n" x y v in *)
  let r = if v <= x then (x +. y) /. 2. else v in
  (* let _ = Printf.printf "round_down: %f\n" r in *)
  r
;;

let random x y = if equal x y then x else x +. Random.float (y -. x)
let from_int = float_of_int
