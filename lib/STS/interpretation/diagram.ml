(** ROBDD-based backend for the symbolic transition systems. *)
open Common.Prelude

open Def

module Order = struct
  open Ppx_compare_lib.Builtin

  module Level = struct
    type t = Level of int [@@deriving compare]
  end

  open Level

  let any = Level 3
  let lv2 = Level 2
  let lv1 = Level 1
  let lv0 = Level 0
  let min (Level x) (Level y) = Level (Int.min x y)

  let with_ ?except lv x v =
    let lv =
      match except with
      | Some (ext, lv) when ext = v -> lv
      | _ -> lv
    in
    min x lv
  ;;

  let numeric_last ~now atom =
    fold_bool_atom (with_ lv2) (with_ lv1 ~except:(now, lv0)) any atom
  ;;

  let default atom = fold_bool_atom (with_ lv1) (with_ lv0) any atom

  module LvIndMap = Map.Make (struct
      type t = Level.t * int [@@deriving compare]
    end)

  module LvMap = Map.Make (Level)
end

let rec bool_expr_to_bdd = function
  | BAtom a -> Bdd.ithvar a
  | BNot e ->
    let e = bool_expr_to_bdd e in
    Bdd.dnot e
  | BAnd es ->
    let es = List.map bool_expr_to_bdd es in
    List.fold_left Bdd.dand (Bdd.dtrue ()) es
  | BOr es ->
    let es = List.map bool_expr_to_bdd es in
    List.fold_left Bdd.dand (Bdd.dtrue ()) es
  | BEq (x, y) ->
    let x = bool_expr_to_bdd x
    and y = bool_expr_to_bdd y in
    Bdd.eq x y
  | BNeq (x, y) ->
    let x = bool_expr_to_bdd x
    and y = bool_expr_to_bdd y in
    Bdd.dnot @@ Bdd.eq x y
  | BImply (x, y) ->
    let x = bool_expr_to_bdd x
    and y = bool_expr_to_bdd y in
    Bdd.dor (Bdd.dnot x) y
  | BITE { cond; if_true; if_false } ->
    let cond = bool_expr_to_bdd cond
    and if_true = bool_expr_to_bdd if_true
    and if_false = bool_expr_to_bdd if_false in
    Bdd.ite if_true cond if_false
;;

type ('sv, 'iv) t =
  { now : 'iv
  ; atoms : ('sv, 'iv) bool_atom Dynarray.t
  ; guard : Bdd.t
  ; assignments : ('sv, 'iv) assignment list
  }

let of_machine now { guard; assignments; invariant = _ } : _ t =
  let open Order in
  let index = ref LvMap.empty in
  let assign_temp_id expr =
    let lv = Order.numeric_last ~now expr in
    let map, arr = LvMap.value_mut ~default:Dynarray.create lv !index in
    index := map;
    let i = Dynarray.length arr in
    Dynarray.add_last arr expr;
    lv, i
  in
  let guard = map_bool_expr assign_temp_id guard in
  let bool_atoms, remap =
    LvMap.fold
      (fun lv arr (bool_atoms, remap) ->
         let len = Dynarray.length bool_atoms in
         let remap =
           Dynarray.fold_lefti
             (fun remap i _ -> Order.LvIndMap.add (lv, i) (i + len) remap)
             remap
             arr
         in
         Dynarray.append bool_atoms arr;
         bool_atoms, remap)
      !index
      (Dynarray.create (), Order.LvIndMap.empty)
  in
  let guard = map_bool_expr (fun k -> LvIndMap.find k remap) guard in
  let guard = bool_expr_to_bdd guard in
  { now; atoms = bool_atoms; guard; assignments }
;;

let interpret_bdd node = ()

let do_transition
      ~input_to_interface
      ~eval_guard
      { guard; assignments; invariant }
      state
      inputs
  =
  let statei = state_to_interface state in
  let abstract_inputs = input_to_interface inputs in
  let real_inputs = Full.input_to_interface inputs in
  let empty_inputs = empty_input_interface in
  let t = eval_guard statei abstract_inputs guard in
  if t
  then (
    let new_state = apply_assignments statei real_inputs default_state assignments in
    let new_state_int = state_to_interface new_state in
    if Full.eval_bool new_state_int empty_inputs invariant
    then Ok new_state
    else Error FailedInvariant)
  else Error FailedGuard
;;
