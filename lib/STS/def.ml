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
[@@deriving compare, sexp, map, fold]

(** Empty type. It has no constructors and so values cannot exist.
  Used to prune possibilities in polymorphic types.*)
type empty = |

(** Type of Boolean expressions. *)
type 'atom bool_expr =
  | BAtom of 'atom
  | BNot of 'atom bool_expr
  | BAnd of 'atom bool_expr list
  | BOr of 'atom bool_expr list
  | BEq of 'atom bool_expr * 'atom bool_expr
  | BNeq of 'atom bool_expr * 'atom bool_expr
  | BImply of 'atom bool_expr * 'atom bool_expr
  | BITE of ('atom bool_expr, 'atom bool_expr) ite
[@@deriving compare, sexp, map, fold]

type ('sv, 'iv) bool_atom =
  | BConst of bool
  | BStateVar of 'sv
  | BInputVar of 'iv
  | IntComp of ('sv, 'iv) int_expr * num_rel * ('sv, 'iv) int_expr
  | RatComp of ('sv, 'iv) rat_expr * num_rel * ('sv, 'iv) rat_expr
  | IntQueuePositive of 'sv

(** Type of integer expressions. *)
and ('sv, 'iv) int_expr =
  | IConst of int
  | IStateVar of 'sv
  | IInputVar of 'iv
  | IBinOp of ('sv, 'iv) int_expr * num_op * ('sv, 'iv) int_expr
  | IITE of (('sv, 'iv) bool_atom bool_expr, ('sv, 'iv) int_expr) ite
  | IPeekFirstQueue of 'sv
  | IPeekLastQueue of 'sv
  | IntQueueLength of 'sv
  | RatQueueLength of 'sv

(** Type of rational expressions. *)
and ('sv, 'iv) rat_expr =
  | RConst of Rational.t
  | RStateVar of 'sv
  | RInputVar of 'iv
  | RITE of (('sv, 'iv) bool_atom bool_expr, ('sv, 'iv) rat_expr) ite
  | RBinOp of ('sv, 'iv) rat_expr * num_op * ('sv, 'iv) rat_expr
  | RPeekFirstQueue of 'sv
  | RPeekLastQueue of 'sv
[@@deriving compare, sexp, fold]

(** Type of integer queue expressions. *)
type ('sv, 'iv) int_queue_expr =
  | IQVar of 'sv
  | IPushQueue of ('sv, 'iv) int_queue_expr * ('sv, 'iv) int_expr
  | IPopQueue of ('sv, 'iv) int_queue_expr
  | IDecreaseAllQueue of ('sv, 'iv) int_queue_expr
  | IIncreaseAllQueue of ('sv, 'iv) int_queue_expr
  | IQITE of (('sv, 'iv) bool_atom bool_expr, ('sv, 'iv) int_queue_expr) ite
[@@deriving compare]

(** Type of rational queue expressions. *)
type ('sv, 'iv) rat_queue_expr =
  | RQVar of 'sv
  | RPushQueue of ('sv, 'iv) rat_queue_expr * ('sv, 'iv) rat_expr
  | RPopQueue of ('sv, 'iv) rat_queue_expr
  | RQITE of (('sv, 'iv) bool_atom bool_expr, ('sv, 'iv) rat_queue_expr) ite
[@@deriving compare]

(** Type of expressions. *)
type ('sv, 'iv) expr =
  | BoolExpr of ('sv, 'iv) bool_atom bool_expr
  | IntExpr of ('sv, 'iv) int_expr
  | RatExpr of ('sv, 'iv) rat_expr
  | IntQueueExpr of ('sv, 'iv) int_queue_expr
  | RatQueueExpr of ('sv, 'iv) rat_queue_expr
[@@deriving compare]

(** Type of transition guards. *)
type ('sv, 'iv) guard = ('sv, 'iv) bool_atom bool_expr [@@deriving compare]

(** Type of transition assignments. *)
type ('sv, 'iv) assignment = 'sv * ('sv, 'iv) expr [@@deriving compare]

(** Type of abstract machines. *)
type ('sv, 'iv) t =
  { guard : ('sv, 'iv) bool_atom bool_expr
    (** State and input conditions of the form [S -> B^n -> Q^m -> Z^k -> B], where [B^n] encodes the clock ticks, [Q^m] next possible time and rational inputs, [Z^k] integer inputs. *)
  ; assignments : ('sv, 'iv) assignment list
    (** List of actions performed on the state variables using previous state and inputs [S -> B^n -> Q^m -> Z^k -> S]*)
  ; invariant : ('sv, empty) bool_atom bool_expr
    (** Boolean expression encoding state invariant. *)
  }

(** Synchronizes two machines by cartesian product of their transitions and conjunction of invariants. *)
let sync_machines sv_comp iv_comp machines =
  let guards, assignments, invariants =
    List.split3
    @@ List.map
         (fun { guard; assignments; invariant } -> guard, assignments, invariant)
         machines
  in
  let guard = BAnd guards
  and assignments = List.flatten assignments
  and invariant = BAnd invariants in
  let comp_assign = compare_assignment sv_comp iv_comp in
  let assignments = List.sort_uniq comp_assign assignments in
  assert (
    (* checking that there are no duplicate, non equivalent assignments *)
    snd
    @@ List.fold_left
         (fun ((prev, duplicated) as acc) el ->
            if duplicated
            then acc
            else (
              match prev with
              | Some prev ->
                if comp_assign prev el = 0 then Some el, true else Some el, false
              | None -> Some el, false))
         (None, true)
         assignments);
  { guard; assignments; invariant }
;;
