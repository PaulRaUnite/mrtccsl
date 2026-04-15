(** Module of value based interpretation of the abstract machine. *)

open Common
open Prelude
open Number
open Def
include Aux
module Full = Full

(** Applies the assignment, evaluating on the given state and input values, and saves the value in new state. *)
let apply_assignment
      (old_state : var state_interface)
      (inputs : (var, int, Rational.t) input_interface)
      (new_state : state)
      assignment
  =
  let var, expr = assignment in
  match expr with
  | BoolExpr e ->
    { new_state with
      bools = VarMap.add var (Full.eval_bool old_state inputs e) new_state.bools
    }
  | IntExpr e ->
    { new_state with
      integers = VarMap.add var (Full.eval_integer old_state inputs e) new_state.integers
    }
  | RatExpr e ->
    { new_state with
      rationals =
        VarMap.add var (Full.eval_rational old_state inputs e) new_state.rationals
    }
  | IntQueueExpr e ->
    let q = Full.eval_int_queue old_state inputs e in
    { new_state with int_queues = VarMap.add var q new_state.int_queues }
  | RatQueueExpr e ->
    { new_state with
      rat_queues =
        VarMap.add var (Full.eval_rat_queue old_state inputs e) new_state.rat_queues
    }
;;

(** Applies all assignments, evaluating on the given state and input values, and saves values in new state. *)
let apply_assignments old_state inputs new_state assignments =
  List.fold_left
    (fun new_state assgn -> apply_assignment old_state inputs new_state assgn)
    new_state
    assignments
;;

module Partial = Partial

type transition_error =
  | NoValidTransition
  | FailedGuard
  | FailedInvariant

let transition_error_to_string = function
  | NoValidTransition -> "no valid transition"
  | FailedGuard -> "failed guard"
  | FailedInvariant -> "failed invariant"
;;

let do_transition ~input_to_interface ~eval_guard { transitions; invariant } state inputs =
  let statei = state_to_interface state in
  let abstract_inputs = input_to_interface inputs in
  let real_inputs = Full.input_to_interface inputs in
  let empty_inputs = empty_input_interface in
  let transition =
    List.find_opt
      (fun { state_cond; _ } -> Full.eval_bool statei empty_inputs state_cond)
      transitions
  in
  match transition with
  | Some { input_cond; assignments; _ } ->
    let t = eval_guard statei abstract_inputs input_cond in
    if t
    then (
      let new_state = apply_assignments statei real_inputs default_state assignments in
      let new_state_int = state_to_interface new_state in
      if Full.eval_bool new_state_int empty_inputs invariant
      then Ok new_state
      else Error FailedInvariant)
    else Error FailedGuard
  | None -> Error NoValidTransition
;;

(** Full evaluate the step in a transition, expects all variables to have defined values. *)
let apply_transition =
  do_transition ~input_to_interface:Full.input_to_interface ~eval_guard:Full.eval_bool
;;

(** Evaluate the step in a transition, while existentially quantifying the numerical variables. Allows to check specification satisfaction on traces with only timestampts and clocks. *)
let accept_transition =
  do_transition ~input_to_interface:Partial.input_to_interface ~eval_guard:(fun s i c ->
    let t, _ = Partial.eval_bool s i c in
    not @@ Partial.DQZF.is_bottom t)
;;
