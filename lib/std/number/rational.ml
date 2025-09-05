open Prelude
include Mpqf

include Interface.ExpOrder.Make (struct
    include Mpqf

    let compare = cmp
  end)

include Interface.Number.Operators.Make (struct
    include Mpqf

    let zero = of_int 0
    let one = of_int 1
  end)

let sexp_of_t x =
  let nom = get_num x in
  let denom = get_den x in
  Sexplib0.Sexp_conv.(sexp_of_pair sexp_of_int sexp_of_int)
    (Mpz.get_int nom, Mpz.get_int denom)
;;

let t_of_sexp sexp =
  let x, y = Sexplib0.Sexp_conv.(pair_of_sexp int_of_sexp int_of_sexp) sexp in
  of_frac x y
;;

(*TODO: lossy convertion, but low priority*)
let t_to_string x = Float.to_string (to_float x)
let to_string = t_to_string

let round_up step x y =
  let v = x + step in
  let r = if more_eq v y then (x + y) / of_int 2 else v in
  r
;;

let round_down step x y =
  let v = y - step in
  let r = if less_eq v x then (x + y) / of_int 2 else v in
  r
;;

let random l r =
  let denom = Int.add (Random.int 1000) 1 in
  let nom = Random.int denom in
  let nom = of_int nom
  and denom = of_int denom in
  l + ((r - l) * (nom / denom))
;;

let from_int = of_int
let to_rational = Fun.id
let from_pair (nom, denom) = of_frac nom denom

let of_decimal_string s =
  match String.split_on_char '.' s with
  | [ whole; decimal ] ->
    let whole = (from_int << int_of_string) whole in
    let decimal_num = int_of_string decimal in
    let len_after_zero = String.length decimal in
    let decimal = of_frac decimal_num (Int.pow 10 len_after_zero) in
    add whole decimal
  | _ -> failwith "wrong decimal number"
;;

let of_float v =
  if Float.is_nan v
  then failwith "cannot represent nan as rational"
  else if Float.is_infinite v
  then failwith "cannot represent infinity as rational"
  else of_float v
;;

(** [modulo_floor x ~divisor] returns [int(x/divisor), int(x/divisor)*divisor, rem(x/divisor)*divisor]*)
let[@inline] modulo_floor x ~divisor : int * t * t =
  let parts = div x divisor in
  let nom = Mpqf.get_num parts
  and denom = Mpqf.get_den parts in
  let whole, rem = Mpzf.fdiv_qr nom denom in
  Mpz.get_int whole, mul (Mpqf.of_mpz whole) divisor, mul (Mpqf.of_mpz2 rem denom) divisor
;;

let%test_unit "correct modulo floor" =
  [%test_eq: _] (modulo_floor (of_int 1) ~divisor:(of_frac 1 2)) (2, of_int 1, of_int 0)
;;

(** [modulo_ceil x ~divisor] returns [int(x/divisor)+1, (int(x/divisor)+1)*divisor, -rem(x/divisor)*divisor]*)
let[@inline] modulo_ceil x ~divisor : int * t * t =
  let parts = div x divisor in
  let nom = Mpzf.add_int (Mpqf.get_num parts) 1
  and denom = Mpqf.get_den parts in
  let whole, rem = Mpzf.cdiv_qr nom denom in
  Mpz.get_int whole, Mpqf.of_mpz whole * divisor, Mpqf.of_mpz2 rem denom * divisor
;;

let%test_unit "correct modulo ceil" =
  [%test_eq: _] (modulo_ceil (of_int 1) ~divisor:(of_frac 1 2)) (2, of_int 1, of_int 0)
;;

(** [modulo_around x ~divisor] returns [int(x/divisor)+1, (int(x/divisor)+1)*divisor, -rem(x/divisor)*divisor]*)
let[@inline] modulo_near x ~divisor : int * t * t =
  let divisor = div divisor (of_int 2) in
  let parts = div x divisor in
  let nom = Mpzf.add_int (Mpqf.get_num parts) 1
  and denom = Mpqf.get_den parts in
  let whole, rem = Mpzf.fdiv_qr nom denom in
  let whole_int = Mpz.get_int whole in
  let whole_int, rem =
    if whole_int mod 2 = 0
    then Int.div whole_int 2, rem
    else Int.succ (Int.div whole_int 2), Mpzf.neg rem
  in
  whole_int, Mpqf.of_mpz whole * divisor, Mpqf.of_mpz rem * divisor
;;

let%test_unit "correct modulo ceil" =
  [%test_eq: _]
    (modulo_near (of_frac 5 4) ~divisor:(of_int 1))
    (2, of_int 1, of_frac 1 4);
  [%test_eq: _]
    (modulo_near (of_frac 3 4) ~divisor:(of_int 1))
    (2, of_int 1, of_frac (-1) 4)
;;
