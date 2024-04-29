open Prelude
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
  | ZeroCond of ('c, 'n) tag_expr * 'n
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

let rec fold_texp f acc = function
  | TagVar (v, i) -> f (Some v) i acc
  | Op (left, _, right) ->
    let acc = fold_texp f acc left in
    fold_texp f acc right
  | Index i -> f None i acc
  | Const _ -> acc
  | ZeroCond (more, _) -> fold_texp f acc more
;;

let rec fold_bexp f acc = function
  | Or list | And list -> List.fold_left (fold_bexp f) acc list
  | Linear (left, _, right) ->
    let acc = fold_texp f acc left in
    fold_texp f acc right
;;

let rec map_ind_texp f = function
  | TagVar (v, i) -> TagVar (v, f (Some v) i)
  | Index i -> Index (f None i)
  | Const c -> Const c
  | Op (left, op, right) -> Op (map_ind_texp f left, op, map_ind_texp f right)
  | ZeroCond (more, init_value) -> ZeroCond (map_ind_texp f more, init_value)
;;

let rec map_ind_bexp f = function
  | Or list -> Or (List.map (map_ind_bexp f) list)
  | And list -> And (List.map (map_ind_bexp f) list)
  | Linear (left, op, right) -> Linear (map_ind_texp f left, op, map_ind_texp f right)
;;

let rec use_more_cond_texp = function
  | ZeroCond (more, _) -> more
  | Op (l, op, r) -> Op (use_more_cond_texp l, op, use_more_cond_texp r)
  | _ as e -> e
;;

let rec use_more_cond_bexp = function
  | Or list -> Or (List.map use_more_cond_bexp list)
  | And list -> And (List.map use_more_cond_bexp list)
  | Linear (l, op, r) -> Linear (use_more_cond_texp l, op, use_more_cond_texp r)
;;

let rec norm = function
  | Or [] -> And []
  | Or [ x ] -> x
  | Or list ->
    let to_flatten, others =
      List.partition_map
        (fun f ->
          match norm f with
          | Or l -> Either.Left l
          | _ as other -> Either.Right other)
        list
    in
    Or (others @ List.flatten to_flatten)
  | And [ x ] -> x
  | And list ->
    let to_flatten, others =
      List.partition_map
        (fun f ->
          match norm f with
          | And l -> Either.Left l
          | _ as other -> Either.Right other)
        list
    in
    And (others @ List.flatten to_flatten)
  | _ as lin -> lin
;;

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
  | Precedence { cause; effect } -> cause @ i < effect @ i
  | Causality { cause; effect } -> cause @ i <= effect @ i
  | RTdelay { out; arg; delay = e1, e2 } -> (out @ i) - (arg @ i) |> (Const e1, Const e2)
  | Delay { out; arg; delay = d1, d2; base = None } when Stdlib.(d1 = d2) ->
    (out @ Stdlib.(i - d1)) = arg @ i
  | _ -> failwith "unimplemented"
;;

let exact_spec (s : ('c, 'n) specification) : ('c, 'n) bool_expr =
  And (List.map exact_rel s)
;;

(*
   let rec all_variables bexp =
   let tvars = function
   | *)

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
    | TagVar (var, ind) ->
      let ind_str =
        match ind with
        | x when x > 0 -> Printf.sprintf "i+%i" x
        | 0 -> "i"
        | x -> Printf.sprintf "i%i" x
      in
      Printf.sprintf "%s[%s]" (V.to_string var) ind_str
    | Const n -> N.to_string n
    | Index i ->
      (match i with
       | x when x > 0 -> Printf.sprintf "i+%i" x
       | 0 -> "i"
       | x -> Printf.sprintf "i%i" x)
    | Op (l, op, r) ->
      Printf.sprintf
        "(%s %s %s)"
        (string_of_tag_expr l)
        (string_of_num_op op)
        (string_of_tag_expr r)
    | ZeroCond (more, init) ->
      Printf.sprintf "(%s when i>0 else %s)" (string_of_tag_expr more) (N.to_string init)
  ;;

  let string_of_num_rel = function
    | Eq -> "="
    | More -> ">"
    | Less -> "<"
    | MoreEq -> ">="
    | LessEq -> "<="
  ;;

  let string_of_bool_expr =
    let rec aux level =
      let padding = String.make (2 * level) ' ' in
      let concat delim l =
        let s =
          List.fold_left
            (fun acc el ->
              Printf.sprintf "%s\n%s%s %s" acc padding delim (aux (level + 1) el))
            ""
            l
        in
        if List.is_one l || level = 0 then s else Printf.sprintf "(%s\n)" s
      in
      function
      | Or list -> concat "V" list
      | And list -> concat "⋀" list
      | Linear (l, op, r) ->
        Printf.sprintf
          "%s %s %s"
          (string_of_tag_expr l)
          (string_of_num_rel op)
          (string_of_tag_expr r)
    in
    aux 0
  ;;
end
