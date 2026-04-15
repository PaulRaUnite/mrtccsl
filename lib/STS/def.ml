(** Symbolic State Machine definitions. *)

open Common
open Prelude
open Number
open Expr
open Ppx_compare_lib.Builtin
open Ppx_sexp_conv_lib.Conv

(** Generic if-then-else type. *)
type ('bool, 'expr) ite =
  { cond : 'bool (** If guard. *)
  ; if_true : 'expr (** To be evaluated when the condition is true. *)
  ; if_false : 'expr (** To be evaluated when the condition is false. *)
  }
[@@deriving compare, sexp]

(** Empty type. It has no constructors and so values cannot exist.
  Used to prune possibilities in polymorphic types.*)
type empty = |

(** Type of Boolean expressions. *)
type ('sv, 'iv) bool_expr =
  | BConst of bool
  | BStateVar of 'sv
  | BInputVar of 'iv
  | BNot of ('sv, 'iv) bool_expr
  | BAnd of ('sv, 'iv) bool_expr list
  | BOr of ('sv, 'iv) bool_expr list
  | BEq of ('sv, 'iv) bool_expr * ('sv, 'iv) bool_expr
  | BNeq of ('sv, 'iv) bool_expr * ('sv, 'iv) bool_expr
  | BImply of ('sv, 'iv) bool_expr * ('sv, 'iv) bool_expr
  | IntComp of ('sv, 'iv) int_expr * num_rel * ('sv, 'iv) int_expr
  | RatComp of ('sv, 'iv) rat_expr * num_rel * ('sv, 'iv) rat_expr
  | BITE of (('sv, 'iv) bool_expr, ('sv, 'iv) bool_expr) ite
  | IntQueuePositive of 'sv

(** Type of integer expressions. *)
and ('sv, 'iv) int_expr =
  | IConst of int
  | IStateVar of 'sv
  | IInputVar of 'iv
  | IBinOp of ('sv, 'iv) int_expr * num_op * ('sv, 'iv) int_expr
  | IITE of (('sv, 'iv) bool_expr, ('sv, 'iv) int_expr) ite
  | IPeekFirstQueue of 'sv
  | IPeekLastQueue of 'sv
  | IntQueueLength of 'sv
  | RatQueueLength of 'sv

(** Type of rational expressions. *)
and ('sv, 'iv) rat_expr =
  | RConst of Rational.t
  | RStateVar of 'sv
  | RInputVar of 'iv
  | RITE of (('sv, 'iv) bool_expr, ('sv, 'iv) rat_expr) ite
  | RBinOp of ('sv, 'iv) rat_expr * num_op * ('sv, 'iv) rat_expr
  | RPeekFirstQueue of 'sv
  | RPeekLastQueue of 'sv
[@@deriving compare, sexp]

(** Type of integer queue expressions. *)
type ('sv, 'iv) int_queue_expr =
  | IQVar of 'sv
  | IPushQueue of ('sv, 'iv) int_queue_expr * ('sv, 'iv) int_expr
  | IPopQueue of ('sv, 'iv) int_queue_expr
  | IDecreaseAllQueue of ('sv, 'iv) int_queue_expr
  | IIncreaseAllQueue of ('sv, 'iv) int_queue_expr
  | IQITE of (('sv, 'iv) bool_expr, ('sv, 'iv) int_queue_expr) ite
[@@deriving compare]

(** Type of rational queue expressions. *)
type ('sv, 'iv) rat_queue_expr =
  | RQVar of 'sv
  | RPushQueue of ('sv, 'iv) rat_queue_expr * ('sv, 'iv) rat_expr
  | RPopQueue of ('sv, 'iv) rat_queue_expr
  | RQITE of (('sv, 'iv) bool_expr, ('sv, 'iv) rat_queue_expr) ite
[@@deriving compare]

(** Type of expressions. *)
type ('sv, 'iv) expr =
  | BoolExpr of ('sv, 'iv) bool_expr
  | IntExpr of ('sv, 'iv) int_expr
  | RatExpr of ('sv, 'iv) rat_expr
  | IntQueueExpr of ('sv, 'iv) int_queue_expr
  | RatQueueExpr of ('sv, 'iv) rat_queue_expr
[@@deriving compare]

(** Type of transition guards. *)
type ('sv, 'iv) guard = ('sv, 'iv) bool_expr [@@deriving compare]

(** Type of transition assignments. *)
type ('sv, 'iv) assignment = 'sv * ('sv, 'iv) expr [@@deriving compare]

(** Transition type. Consists of conditions on state (preselect), inputs and state, and state update. *)
type ('sv, 'iv) transition =
  { state_cond : ('sv, empty) bool_expr
    (** Condition on state variables that identifies the partition. *)
  ; input_cond : ('sv, 'iv) bool_expr
    (** Input condition of the form [S -> 2^(B^n * Q)], where [B^n] encodes the clock ticks and [Q] encodes next possible time. *)
  ; assignments : ('sv, 'iv) assignment list
    (** List of actions performed on the state variables using previous state and inputs [S * B^n * Q -> S]*)
  }

(** Synchronizes two transitions into a new transition. A conjunction of conditions, union of assignments. *)
let sync_transitions
      { state_cond = s1; input_cond = in1; assignments = asgn1 }
      { state_cond = s2; input_cond = in2; assignments = asgn2 }
  =
  let assignments = List.sort_uniq compare (List.append asgn1 asgn2) in
  assert (
    (* checking that there are no duplicate, non equivalent assignments *)
    snd
    @@ List.fold_left
         (fun ((prev, duplicated) as acc) el ->
            if duplicated
            then acc
            else (
              match prev with
              (*FIXME: I use polymorphic equality here, should be fine, but better to replace it when functor is introduced. *)
              | Some prev -> if prev = el then Some el, true else Some el, false
              | None -> Some el, false))
         (None, true)
         assignments);
  { state_cond = BAnd [ s1; s2 ]; input_cond = BAnd [ in1; in2 ]; assignments }
;;

(** Type of abstract machines. *)
type ('sv, 'iv) t =
  { transitions : ('sv, 'iv) transition list
  ; invariant : ('sv, empty) bool_expr
  }

(** Synchronizes two machines by cartesian product of their transitions and conjunction of invariants. *)
let sync_machines
      { transitions = t1; invariant = in1 }
      { transitions = t2; invariant = in2 }
  =
  let transitions = List.cartesian t1 t2 |> List.map (Tuple.fn2 sync_transitions) in
  { transitions; invariant = BAnd [ in1; in2 ] }
;;
