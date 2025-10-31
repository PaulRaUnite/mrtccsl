open Prelude
include Mpqf
open Sexplib0.Sexp_conv

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
let t_to_string x = Printf.sprintf "%f" (to_float x)
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

let to_rational = Fun.id
let from_pair (nom, denom) = of_frac nom denom

let of_decimal_string s =
  match String.split_on_char '.' s with
  | [ whole; decimal ] ->
    let whole = (of_int << int_of_string) whole in
    let decimal_num = int_of_string decimal in
    let len_after_zero = String.length decimal in
    let decimal = of_frac decimal_num (Int.pow 10 len_after_zero) in
    add whole decimal
  | [ whole ] -> of_int (int_of_string whole)
  | _ -> failwithf "wrong decimal number: %s" s
;;

let of_float v =
  if Float.is_nan v
  then failwith "cannot represent nan as rational"
  else if Float.is_infinite v
  then failwith "cannot represent infinity as rational"
  else of_float v
;;

let compare_int = Int.compare

(** [modulo_floor x ~divisor] returns [int(x/divisor), int(x/divisor)*divisor, rem(x/divisor)*divisor]*)
let[@inline] modulo_floor x ~divisor : int * t * t =
  let parts = div x divisor in
  let nom = Mpqf.get_num parts
  and denom = Mpqf.get_den parts in
  let whole, rem = Mpzf.fdiv_qr nom denom in
  Mpz.get_int whole, Mpqf.of_mpz whole * divisor, Mpqf.of_mpz2 rem denom * divisor
;;

let%test_unit "correct modulo floor" =
  [%test_eq: int * t * t]
    (modulo_floor (of_int 1) ~divisor:(of_frac 1 2))
    (2, of_int 1, of_int 0);
  [%test_eq: int * t * t]
    (modulo_floor (of_frac 5 4) ~divisor:(of_frac 1 2))
    (2, of_int 1, of_frac 1 4);
  [%test_eq: int * t * t]
    (modulo_floor (of_int (-1)) ~divisor:(of_frac 1 2))
    (-2, of_int (-1), of_int 0);
  [%test_eq: int * t * t]
    (modulo_floor (of_frac (-5) 4) ~divisor:(of_frac 1 2))
    (-3, of_frac (-3) 2, of_frac 1 4)
;;

(** [modulo_ceil x ~divisor] returns [int(x/divisor)+1, (int(x/divisor)+1)*divisor, -rem(x/divisor)*divisor]*)
let[@inline] modulo_ceil x ~divisor : int * t * t =
  let parts = div x divisor in
  let nom = Mpqf.get_num parts
  and denom = Mpqf.get_den parts in
  let whole, rem = Mpzf.cdiv_qr nom denom in
  Mpz.get_int whole, Mpqf.of_mpz whole * divisor, Mpqf.of_mpz2 rem denom * divisor
;;

let%test_unit "correct modulo ceil" =
  [%test_eq: int * t * t]
    (modulo_ceil (of_int 1) ~divisor:(of_frac 1 2))
    (2, of_int 1, of_int 0);
  [%test_eq: int * t * t]
    (modulo_ceil (of_frac 5 4) ~divisor:(of_frac 1 2))
    (3, of_frac 3 2, of_frac (-1) 4);
  [%test_eq: int * t * t]
    (modulo_ceil (of_int (-1)) ~divisor:(of_frac 1 2))
    (-2, of_int (-1), of_int 0);
  [%test_eq: int * t * t]
    (modulo_ceil (of_frac (-5) 4) ~divisor:(of_frac 1 2))
    (-2, of_int (-1), of_frac (-1) 4)
;;

(** [modulo_near x ~divisor] returns closest whole number dividend.*)
let[@inline] modulo_near x ~divisor : int * t * t =
  let divisor = div divisor (of_int 2) in
  let parts = div x divisor in
  let nom = Mpqf.get_num parts
  and denom = Mpqf.get_den parts in
  let whole, rem = Mpzf.fdiv_qr nom denom in
  let whole_int = Mpz.get_int whole in
  let whole_int, rem =
    if whole_int mod 2 = 0
    then Int.div whole_int 2, rem
    else Int.succ (Int.div whole_int 2), Mpzf.neg rem
  in
  whole_int, Mpqf.of_int (Int.mul whole_int 2) * divisor, Mpqf.of_mpz2 rem denom * divisor
;;

let modulo_near x ~divisor =
  if Int.mul (sgn x) (sgn divisor) = -1
  then (
    let whole_int, whole, rem = modulo_near (neg x) ~divisor in
    Int.neg whole_int, neg whole, neg rem)
  else modulo_near x ~divisor
;;

let%test_unit "correct modulo near+" =
  [%test_eq: int * t * t]
    (modulo_near (of_frac 5 4) ~divisor:(of_int 1))
    (1, of_int 1, of_frac 1 4);
  [%test_eq: int * t * t]
    (modulo_near (of_frac 3 4) ~divisor:(of_int 1))
    (1, of_int 1, of_frac (-1) 4);
  [%test_eq: int * t * t]
    (modulo_near (of_frac 7 4) ~divisor:(of_int 1))
    (2, of_int 2, of_frac (-1) 4);
  [%test_eq: int * t * t]
    (modulo_near (of_frac 9 4) ~divisor:(of_int 1))
    (2, of_int 2, of_frac 1 4)
;;

let%test_unit "correct modulo near-" =
  [%test_eq: int * t * t]
    (modulo_near (of_frac (-5) 4) ~divisor:(of_int 1))
    (-1, of_int (-1), of_frac (-1) 4);
  [%test_eq: int * t * t]
    (modulo_near (of_frac (-3) 4) ~divisor:(of_int 1))
    (-1, of_int (-1), of_frac 1 4);
  [%test_eq: int * t * t]
    (modulo_near (of_frac (-7) 4) ~divisor:(of_int 1))
    (-2, of_int (-2), of_frac 1 4);
  [%test_eq: int * t * t]
    (modulo_near (of_frac (-9) 4) ~divisor:(of_int 1))
    (-2, of_int (-2), of_frac (-1) 4)
;;

let round_with modulo bin_size x =
  let _, closest_whole, _ = modulo x ~divisor:bin_size in
  closest_whole
;;

let round_near = round_with modulo_near
let round_floor = round_with modulo_floor
let round_ceil = round_with modulo_ceil
let of_string = of_decimal_string

let to_int n =
  let nom, denom = to_mpzf2 n in
  let result = Mpzf.fdiv_q nom denom in
  Mpz.get_int result
;;

let pp fmt x = Format.pp_print_string fmt (to_string x)
