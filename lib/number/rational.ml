open Prelude
include Num

include ExpOrder.Make (struct
    include Num

    type t = num

    let compare = compare_num
  end)

let zero = num_of_int 0
let ( + ) = add_num
let ( - ) = sub_num
let neg = minus_num

let sexp_of_t x =
  let r = ratio_of_num x in
  let nom = Big_int.int_of_big_int @@ Ratio.numerator_ratio r in
  let denom = Big_int.int_of_big_int @@ Ratio.denominator_ratio r in
  Sexplib0.Sexp_conv.(sexp_of_pair sexp_of_int sexp_of_int) (nom, denom)
;;

let t_of_sexp sexp =
  let x, y = Sexplib0.Sexp_conv.(pair_of_sexp int_of_sexp int_of_sexp) sexp in
  let x = num_of_int x
  and y = num_of_int y in
  x // y
;;

let rec bigint_gcd a b =
  if Big_int.eq_big_int b Big_int.zero_big_int
  then a
  else bigint_gcd b (Big_int.mod_big_int a b)
;;

let t_to_string x =
  let r = ratio_of_num x in
  let nom = Ratio.numerator_ratio r in
  let denom = Ratio.denominator_ratio r in
  let gcd = bigint_gcd denom (Big_int.big_int_of_int 10) in
  let whole, rem = Big_int.quomod_big_int nom denom in
  let whole_str = Big_int.string_of_big_int whole in
  if gcd != Big_int.unit_big_int
  then
    Printf.sprintf
      "%s.%s"
      whole_str
      (Big_int.string_of_big_int (Big_int.mult_big_int gcd rem))
  else if Big_int.eq_big_int Big_int.zero_big_int rem
  then whole_str
  else
    Printf.sprintf
      "%s+%s/%s"
      whole_str
      (Big_int.string_of_big_int rem)
      (Big_int.string_of_big_int denom)
;;

let round_up step x y =
  let v = x +/ step in
  let r = if v >=/ y then (x +/ y) // num_of_int 2 else v in
  (* let _ = Printf.printf "%s" (t_to_string r) in *)
  r
;;

let round_down step x y =
  let v = y -/ step in
  (* let _ = Printf.printf "v: %s %s %s" (t_to_string x) (t_to_string y) (t_to_string v) in *)
  let r = if v <=/ x then (x +/ y) // num_of_int 2 else v in
  (* let _ = Printf.printf "round_down: %s\n" (t_to_string r) in *)
  r
;;

let random l r =
  let denom = Random.int 1097 in
  let nom = Random.int (Int.add denom 1) in
  let nom = num_of_int nom
  and denom = num_of_int denom in
  l +/ ((r -/ l) */ (nom // denom))
;;

let from_int = num_of_int
