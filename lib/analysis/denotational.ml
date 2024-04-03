open Sexplib0.Sexp_conv

type num_op =
  | Add
  | Sub
  | Mul
  | Div
[@@deriving sexp]

type ('c, 'n) tag_expr =
  | TagVar of 'c * int
  | Const of 'n
  | Index of int
  | Op of ('c, 'n) tag_expr * num_op * ('c, 'n) tag_expr
[@@deriving sexp]

type num_rel =
  | Eq
  | More
  | Less
  | MoreEq
  | LessEq
[@@deriving sexp]

type ('c, 'n) bool_expr =
  | Or of ('c, 'n) bool_expr list
  | And of ('c, 'n) bool_expr list
  | Linear of ('c, 'n) tag_expr * num_rel * ('c, 'n) tag_expr
[@@deriving sexp]

module Syntax = struct
  let ( @ ) c i = TagVar (c, i)
  let ( < ) x y = Linear (x, Less, y)
  let ( <= ) x y = Linear (x, LessEq, y)
  let ( > ) x y = Linear (x, More, y)
  let ( >= ) x y = Linear (x, MoreEq, y)
  let ( = ) x y = Linear (x, Eq, y)
  let ( + ) x y = Op (x, Add, y)
  let ( - ) x y = Op (x, Sub, y)
  let ( * ) x y = Op (x, Mul, y)
  let ( / ) x y = Op (x, Div, y)
  let ( |> ) expr (l, r) = And [ l <= expr; expr <= r ]
end

open Rtccsl

let exact_rel c =
  let open Syntax in
  let i = 0 in
  (*dummy variable*)
  match c with
  | Precedence (a, b) -> a @ i < b @ i
  | Causality (a, b) -> a @ i <= b @ i
  | RTdelay (arg, out, (e1, e2)) -> ((out @ i) - (arg @ i)) |> (Const e1, Const e2)
  | _ -> failwith "unimplemented"
;;

let exact_spec (s : ('c, 'n) specification) : ('c, 'n) bool_expr =
  And (List.map exact_rel s)
;;
