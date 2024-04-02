open Prelude

module Float = struct
  include Float
  include ExpOrder.Make (Float)

  let zero = Float.zero
  let ( + ) = Float.add
  let ( - ) = Float.sub
  let neg = Float.neg
  let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_float
  let t_of_sexp = Sexplib0.Sexp_conv.float_of_sexp
  let t_to_string x = Printf.sprintf "%g" x

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

  let random x y = if Float.equal x y then x else x +. Random.float (y -. x)
end

module Ratio = struct
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

  let t_to_string = string_of_num

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
end
