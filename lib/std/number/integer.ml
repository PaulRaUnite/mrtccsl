open! Prelude
include Int

include Interface.ExpOrder.Make (struct
    include Int

    type t = int

    let compare = Int.compare
  end)

open Sexplib0.Sexp_conv

let sexp_of_t = sexp_of_int
let t_of_sexp = int_of_sexp
let t_to_string = to_string
let random x y = Random.int_in_range ~min:x ~max:y
let round_up = Fun.id
let round_down = Fun.id
let from_int = Fun.id

include Interface.Number.Operators.Make (Int)

let to_rational = Rational.of_int
let of_string = int_of_string