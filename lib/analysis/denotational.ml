type num_op =
  | Add
  | Sub
  | Mul
  | Div

type ('c, 'n) tag_expr =
  | TagVar of 'c * int
  | Const of 'n
  | Index of int
  | Op of ('c, 'n) tag_expr * num_op * ('c, 'n) tag_expr

type num_rel =
  | Eq
  | More
  | Less
  | MoreEq
  | LessEq

type ('c, 'n) bool_expr =
  | Or of ('c, 'n) bool_expr list
  | And of ('c, 'n) bool_expr list
  | Linear of ('c, 'n) tag_expr * num_rel * ('c, 'n) tag_expr

open Rtccsl

let exact_rel c =
  let i = 0 in
  (*dummy variable*)
  match c with
  | Precedence (a, b) -> Linear (TagVar (a, i), Less, TagVar (b, i))
  | Causality (a, b) -> Linear (TagVar (a, i), LessEq, TagVar (b, i))
  | _ -> failwith "unimplemented"
;;

let exact_spec (s : ('c, 'n) specification) : ('c, 'n) bool_expr =
  And (List.map exact_rel s)
;;
