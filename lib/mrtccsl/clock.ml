open Prelude

module String = struct
  include String

  let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_string
  let t_of_sexp = Sexplib0.Sexp_conv.string_of_sexp
  let to_string x = x
end
