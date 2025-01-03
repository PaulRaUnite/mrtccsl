open Prelude
include Mpqf

include Interface.ExpOrder.Make (struct
    include Mpqf

    let compare = cmp
  end)

let zero = of_int 0
let one = of_int 1
let ( + ) = add
let ( - ) = sub
let ( * ) = mul
let ( / ) = div

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

let t_to_string x =
  let nom = get_num x in
  let denom = get_den x in
  let whole, rem = Mpzf.tdiv_qr nom denom in
  let whole_str = Mpzf.to_string whole in
  if Mpzf.cmp (Mpzf.of_int 0) rem = 0
  then whole_str
  else (
    let closest_ten =
      Seq.ints 0
      |> Seq.map (fun exp ->
        let n = Mpz.init () in
        let _ = Mpz.ui_pow_ui n 10 exp in
        n)
      |> Seq.find (fun x ->
        let div = Mpzf.divexact denom x in
        Mpzf.cmp (Mpzf.of_int 0) div = 0 || Mpzf.cmp (Mpzf.of_int 1) div = 0)
      |> Option.get
    in
    let gcd = Mpzf.gcd denom closest_ten in
    if gcd != Mpzf.of_int 1
    then
      Printf.sprintf
        "%s.%s"
        whole_str
        (Mpzf.to_string (Mpzf.mul rem (Mpzf.divexact closest_ten gcd)))
    else Printf.sprintf "%s+%s/%s" whole_str (Mpzf.to_string rem) (Mpzf.to_string denom))
;;

let round_up step x y =
  let v = x + step in
  let r = if more_eq v y then (x + y) / of_int 2 else v in
  (* let _ = Printf.printf "%s" (t_to_string r) in *)
  r
;;

let round_down step x y =
  let v = y - step in
  (* let _ = Printf.printf "v: %s %s %s" (t_to_string x) (t_to_string y) (t_to_string v) in *)
  let r = if less_eq v x then (x + y) / of_int 2 else v in
  (* let _ = Printf.printf "round_down: %s\n" (t_to_string r) in *)
  r
;;

let random l r =
  let denom = Random.int 1097 in
  let nom = Random.int (Int.add denom 1) in
  let nom = of_int nom
  and denom = of_int denom in
  l + ((r - l) * (nom / denom))
;;

let from_int = of_int
let to_rational = Fun.id

(* TODO: is there another way to make it? Looks not performant. *)
let from_pair nom denom = div (from_int nom) (from_int denom)

let of_decimal_string s =
  match String.split_on_char '.' s with
  | [ whole; decimal ] ->
    let whole = (from_int << int_of_string) whole in
    let decimal_num = int_of_string decimal in
    let len_after_zero = String.length decimal in
    let decimal = from_pair decimal_num len_after_zero in
    add whole decimal
  | _ -> failwith "wrong decimal number"
;;