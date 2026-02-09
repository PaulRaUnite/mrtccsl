(** Numeric unary operations. *)
type num_unop =
  [ `Neg (** [-x]*)
  | `Floor (** [floor(x)]*)
  | `Ceil (** [ceil(x)]*)
  | `Round (** [round(x)]*)
  ]
[@@deriving sexp, compare, show]

(** Numeric binary operations. *)
type num_op =
  [ `Add (** [x + y] *)
  | `Sub (** [x - y] *)
  | `Mul (** [x * y] *)
  | `Div (** [x / y] *)
  ]
[@@deriving sexp, compare, show]

(** String representation of binary numeric operations. *)
let string_of_num_op = function
  | `Add -> "+"
  | `Sub -> "-"
  | `Mul -> "*"
  | `Div -> "/"
;;

(** Reduced set of numeric relations. *)
type reduced_num_rel =
  [ `Less (** < *)
  | `LessEq (** <= *)
  | `Eq (** = *)
  ]
[@@deriving sexp, compare, show]

(** Numeric relations. *)
type num_rel =
  [ reduced_num_rel
  | `More (** > *)
  | `MoreEq (** >= *)
  | `Neq (* != *)
  ]
[@@deriving sexp, compare, show]

(** String representation of numeric relations. *)
let string_of_num_rel = function
  | `Neq -> "<>"
  | `Eq -> "="
  | `More -> ">"
  | `Less -> "<"
  | `MoreEq -> ">="
  | `LessEq -> "<="
;;

(** Execute the relation between operands, using the domains [~compare] function. *)
let do_rel ~compare op a b =
  let open Number.Integer.Operators in
  match op with
  | `Less -> compare a b < 0
  | `LessEq -> compare a b <= 0
  | `Eq -> compare a b = 0
  | `More -> compare a b > 0
  | `MoreEq -> compare a b >= 0
  | `Neq -> compare a b <> 0
;;

(** Relation negation. *)
let invert = function
  | `Less -> `MoreEq
  | `LessEq -> `More
  | `Eq -> `Neq
  | `More -> `LessEq
  | `MoreEq -> `Less
  | `Neq -> `Eq
;;

(** Flips the relation. Used in normalization. *)
let flip = function
  | `Less -> `More
  | `LessEq -> `MoreEq
  | `Eq -> `Eq
  | `More -> `Less
  | `MoreEq -> `LessEq
  | `Neq -> `Neq
;;
