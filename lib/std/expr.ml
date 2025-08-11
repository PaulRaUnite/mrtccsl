type num_unop =
  [ `Neg
  | `Floor
  | `Ceil
  | `Round
  ]
[@@deriving sexp, compare, show]

type num_op =
  [ `Add
  | `Sub
  | `Mul
  | `Div
  ]
[@@deriving sexp, compare, show]

let string_of_num_op = function
  | `Add -> "+"
  | `Sub -> "-"
  | `Mul -> "*"
  | `Div -> "/"
;;

type num_rel =
  [ `Less (** < *)
  | `LessEq (** <= *)
  | `Eq (** = *)
  | `More (** > *)
  | `MoreEq (** >= *)
  | `Neq (* != *)
  ]
[@@deriving sexp, compare, show]

let string_of_num_rel = function
  | `Neq -> "<>"
  | `Eq -> "="
  | `More -> ">"
  | `Less -> "<"
  | `MoreEq -> ">="
  | `LessEq -> "<="
;;

let do_rel comp op a b =
  let open Number.Integer.Operators in
  match op with
  | `Less -> comp a b < 0
  | `LessEq -> comp a b <= 0
  | `Eq -> comp a b = 0
  | `More -> comp a b > 0
  | `MoreEq -> comp a b >= 0
  | `Neq -> comp a b <> 0
;;

let invert = function
  | `Less -> `MoreEq
  | `LessEq -> `More
  | `Eq -> `Neq
  | `More -> `LessEq
  | `MoreEq -> `Less
  | `Neq -> `Eq
;;

let swap = function
  | `Less -> `More
  | `LessEq -> `MoreEq
  | `Eq -> `Eq
  | `More -> `Less
  | `MoreEq -> `LessEq
  | `Neq -> `Neq
;;
