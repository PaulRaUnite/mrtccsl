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
  | RTdelay (arg, out, (e1, e2)) -> (out @ i) - (arg @ i) |> (Const e1, Const e2)
  | Delay (out, arg, (d1, d2), Some base) when Stdlib.(d1 = d2 && arg = base) ->
    out @ Int.sub i d1 = arg @ i
  | _ -> failwith "unimplemented"
;;

let exact_spec (s : ('c, 'n) specification) : ('c, 'n) bool_expr =
  And (List.map exact_rel s)
;;
(* 
let rec all_variables bexp = 
  let tvars = function
  |  *)

open Prelude

module type Var = sig
  include Sexplib0.Sexpable.S
  include Stringable with type t := t
end

module type Num = sig
  include Sexplib0.Sexpable.S
  include Stringable with type t := t

  val zero : t
end

module MakeDebug (V : Var) (N : Num) = struct
  let string_of_num_op = function
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
  ;;

  let rec string_of_tag_expr = function
    | TagVar (var, ind) -> Printf.sprintf "%s[%i]" (V.to_string var) ind
    | Const n -> N.to_string n
    | Index i -> Int.to_string i
    | Op (l, op, r) ->
      Printf.sprintf
        "(%s %s %s)"
        (string_of_tag_expr l)
        (string_of_num_op op)
        (string_of_tag_expr r)
  ;;

  let string_of_num_rel = function
    | Eq -> "="
    | More -> ">"
    | Less -> "<"
    | MoreEq -> ">="
    | LessEq -> "<="
  ;;

  let rec string_of_bool_expr = function
    | Or list ->
      List.fold_left
        (fun acc el -> Printf.sprintf "( %s V %s)" acc (string_of_bool_expr el))
        ""
        list
    | And list ->
      List.fold_left
        (fun acc el -> Printf.sprintf "( %s /\\ %s)" acc (string_of_bool_expr el))
        ""
        list
    | Linear (l, op, r) ->
      Printf.sprintf
        "(%s %s %s)"
        (string_of_tag_expr l)
        (string_of_num_rel op)
        (string_of_tag_expr r)
  ;;
end
