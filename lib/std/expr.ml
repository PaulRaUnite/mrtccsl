
type num_op =
  | Add
  | Sub
  | Mul
  | Div
[@@deriving sexp, compare, show]

type num_rel =
  | Neq
  | Eq
  | More
  | Less
  | MoreEq
  | LessEq
[@@deriving sexp, compare, show]
