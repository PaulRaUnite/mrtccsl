open Prelude
include Int

include ExpOrder.Make (struct
    include Int

    type t = int

    let compare = Int.compare
  end)

open Sexplib0.Sexp_conv

let sexp_of_t = sexp_of_int
let t_of_sexp = int_of_sexp
let t_to_string = to_string
let random = Random.int
let round_up = id
let round_down = id

let from_int = id

let ( + ) = ( + )
let ( - ) = ( - )