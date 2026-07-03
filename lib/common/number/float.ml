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
  r
;;

let round_down step x y =
  let v = y -. step in
  let r = if v <= x then (x +. y) /. 2. else v in
  r
;;

let random x y = if equal x y then x else x +. Random.float (y -. x)
let of_int = float_of_int
let to_int = int_of_float
let of_float x = x
let to_float x = x
let of_string = float_of_string
let of_pair (nom, denom) = of_int nom /. of_int denom

(* TODO: refactor out distributions to numbers *)
let factor = 1000.0

let truncated_distribution ~a ~b ~cdf ~ppf =
  let a, b = factor *. a, factor *. b in
  let prob_l, prob_r = Prelude.Tuple.map2 cdf (a, b) in
  if abs (prob_r -. prob_l) < 0.000001
  then Random.float (b -. a) +. a
  else (
    let sample_prob = Owl.Stats.uniform_rvs ~a:prob_l ~b:prob_r in
    let result = ppf sample_prob in
    result /. factor)
;;

let truncated_guassian_rvs ~a ~b ~mu ~sigma =
  if equal sigma 0.0
  then mu
  else (
    let mu, sigma = factor *. mu, factor *. sigma in
    let cdf = Owl.Stats.gaussian_cdf ~mu ~sigma in
    let ppf = Owl.Stats.gaussian_ppf ~mu ~sigma in
    truncated_distribution ~a ~b ~cdf ~ppf)
;;

let truncated_exponential_rvs ~a ~b ~rate =
  let lambda = rate /. factor in
  let cdf = Owl.Stats.exponential_cdf ~lambda in
  let ppf = Owl.Stats.exponential_ppf ~lambda in
  let result = truncated_distribution ~a ~b ~cdf ~ppf in
  result
;;

let exponential_rvs ~rate = Owl.Stats.exponential_rvs ~lambda:rate
