open Prelude

module Float = struct
  include ExpOrder.Make (Float)

  let zero = Float.zero
  let ( + ) = Float.add
  let ( - ) = Float.sub
  let neg = Float.neg
  let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_float
  let t_of_sexp = Sexplib0.Sexp_conv.float_of_sexp
  let t_to_string x = Printf.sprintf "%g" x
end
