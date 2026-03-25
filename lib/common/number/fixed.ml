open Prelude

module type R = sig
  (** Number of decimal points fixed-point number can hold. [resolution >= 0] *)
  val resolution : int
end

(** Functor of a fixed-point precision numbers with scale set using [n=R.resolution]: [10^n]. Condition: [n >= 0].*)
module Make (R : R) = struct
  let resolution = R.resolution
  let scale = Z.pow (Z.of_int 10) R.resolution

  type t = Z.t

  let zero = Z.zero
  let one = scale
  let minus_one = Z.neg Z.one
  let neg x = Z.neg x
  let add x y = Z.add x y
  let ( + ) = add
  let sub x y = Z.sub x y
  let ( - ) = sub
  let compare = Z.compare

  let to_string x =
    if resolution = 0
    then Z.to_string x
    else (
      let s = Z.to_string x in
      let len = String.length s in
      let b = Bytes.make (Int.succ len) '.' in
      let before = Int.sub len resolution in
      Bytes.blit_string s 0 b 0 before;
      Bytes.blit_string s before b (Int.succ before) resolution;
      Bytes.to_string b)
  ;;

  exception WrongFormat of string

  let of_string s =
    if resolution = 0
    then Z.of_string s
    else (
      match String.split_on_char '.' s with
      | [ whole ] -> Z.mul (Z.of_string whole) scale
      | [ whole; decimal ] ->
        let whole = Z.of_string whole
        and decimal = Z.of_string decimal in
        Z.add (Z.mul whole scale) decimal
      | _ -> raise (WrongFormat s))
  ;;

  let t_of_sexp sexp = of_string @@ Sexplib0.Sexp_conv.string_of_sexp sexp
  let sexp_of_t x = Sexplib0.Sexp_conv.sexp_of_string @@ to_string x
  let of_int x = Z.mul (Z.of_int x) scale
  let of_float x = Z.of_float (Float.mul x (Z.to_float scale))

  exception NondivisibleRationalDenominator

  let of_rat_exact Q.{ num; den } =
    let divisor, rem = Z.div_rem scale den in
    if Z.equal rem Z.zero
    then Z.mul num divisor
    else raise NondivisibleRationalDenominator
  ;;

  let succ x = Z.succ x
  let pred x = Z.pred x
end

let%test_module _ =
  (module struct
    module N = Make (struct
        let resolution = 3
      end)

    let%test_unit "conversion int 1" = [%test_eq: N.t] N.(of_int 1) N.(one)
    let%test_unit "conversion float 1" = [%test_eq: N.t] N.(of_float 1.0) N.(one)
    let%test_unit "conversion rational 1" = [%test_eq: N.t] N.(of_rat_exact Q.one) N.(one)

    let%test_unit "conversion rational 0.001" =
      [%test_eq: N.t] N.(of_rat_exact @@ Q.of_ints 1 1000) N.(succ zero)
    ;;

    let%test_unit "addition" =
      [%test_eq: N.t] N.(of_int 1 + of_int 2) N.(of_int 3);
      [%test_eq: N.t] N.(of_int 1 + of_int 2) N.(of_int 3);
      [%test_eq: N.t] N.(of_int 1 + of_int 2) N.(of_int 3)
    ;;
  end)
;;
