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
    fold_bool_atom (with_ lv0) (with_ lv1 ~except:(now, lv2)) any atom
  ;;

  let inputs_last ~now:_ atom = fold_bool_atom (with_ lv1) (with_ lv0) any atom

  module LvIndMap = Map.Make (struct
      type t = Level.t * int [@@deriving compare]
    end)

  module LvMap = Map.Make (Level)
end

let rec bool_expr_to_bdd = function
  | BConst c -> if c then Bdd.dtrue () else Bdd.dfalse ()
  | BAtom a -> Bdd.idy a
  | BNot e ->
    let e = bool_expr_to_bdd e in
    Bdd.dnot e
  | BAnd es ->
    let es = List.map bool_expr_to_bdd es in
    List.fold_left Bdd.dand (Bdd.dtrue ()) es
  | BOr es ->
    let es = List.map bool_expr_to_bdd es in
    List.fold_left Bdd.dand (Bdd.dfalse ()) es
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
    Bdd.ite cond if_true if_false
;;

type ('sv, 'iv) t =
  { now : 'iv
  ; atoms : ('sv, 'iv) bool_atom Dynarray.t
  ; guard : Bdd.t
  ; assignments : ('sv, 'iv) assignment list
  }

module AtomIndex = Map.Make (struct
    type t = (string, string) bool_atom

    let compare = compare_bool_atom String.compare String.compare
  end)

let of_machine now { guard; assignments; invariant = _ } : _ t =
  (* print_endline
  @@ Sexplib0.Sexp.to_string_hum
  @@ sexp_of_bool_expr (sexp_of_bool_atom String.sexp_of_t String.sexp_of_t) guard; *)
  let open Order in
  let index = ref LvMap.empty in
  let assign_temp_id expr =
    let lv = Order.numeric_last ~now expr in
    let map = LvMap.value ~default:AtomIndex.empty lv !index in
    let i = AtomIndex.value ~default:(AtomIndex.cardinal map) expr map in
    let map = AtomIndex.add expr i map in
    index := LvMap.add lv map !index;
    lv, i
  in
  let guard = map_bool_expr assign_temp_id guard in
  let bool_atoms, remap =
    LvMap.fold
      (fun lv map (bool_atoms, remap) ->
         let remap =
           AtomIndex.fold
             (fun atom i remap ->
                Dynarray.add_last bool_atoms atom;
                Order.LvIndMap.add (lv, i) (Dynarray.length bool_atoms - 1) remap)
             map
             remap
         in
         bool_atoms, remap)
      !index
      (Dynarray.create (), Order.LvIndMap.empty)
  in
  let guard = map_bool_expr (fun k -> LvIndMap.find k remap) guard in
  let guard = bool_expr_to_bdd guard in
  (* Bdd.print_mons guard; *)
  { now; atoms = bool_atoms; guard; assignments }
;;

module V = struct
  type t = string
end

module E = struct
  let compare_bool = Bool.compare

  type t =
    { complement : bool
    ; label : bool
    ; selected : bool
    }
  [@@deriving compare]

  let default = { complement = false; label = false; selected = false }
end

module G = Graph.Imperative.Digraph.AbstractLabeled (V) (E)

module Dot = Graph.Graphviz.Dot (struct
    include G

    let vertex_name v = string_of_int (V.hash v)
    let graph_attributes _ = []
    let default_vertex_attributes _ = []

    let vertex_attributes v =
      let label = V.label v in
      match label with
      | "0" | "1" -> [ `Label label; `Shape `Box ]
      | _ -> [ `Label label ]
    ;;

    let default_edge_attributes _ = []

    let edge_attributes e =
      let label = G.E.label e in
      [ `Label (string_of_bool label.label)
      ; `Arrowhead (if label.complement then `Dot else `Normal)
      ; `Color (if label.selected then 0xff0000 else 0)
      ]
    ;;

    let get_subgraph _ = None
  end)

let to_dot graph = Dot.output_graph stdout graph
let interpret_bdd _node = ()

(* let do_transition
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
;; *)

(*
TODO:
- structure for the step
  - it should constrain the numerical values
  - should be able to return concrete values
- traversal of the diagram:
  - separate atoms into to be evaluated, decided and constraining
  - define clock strategies on the diagrams  
*)

type var = int

type 'a b =
  | BFalse
  | BTrue
  | BIf of var * 'a * 'a

let inspect bdd =
  if Bdd.is_true bdd
  then BTrue
  else if Bdd.is_false bdd
  then BFalse
  else BIf (Bdd.root_var bdd, Bdd.high_part bdd, Bdd.low_part bdd)
;;

let to_graph { guard; atoms; _ } =
  let labels =
    Dynarray.map
      (fun a ->
         Format.asprintf
           "%a"
           (PP.bool_atom Format.pp_print_string Format.pp_print_string)
           a)
      atoms
  in
  let atom_label i = Dynarray.get labels i in
  let graph = G.create () in
  let v1 = G.V.create "1" in
  let v0 = G.V.create "0" in
  let rec visit bdd =
    match inspect bdd with
    | BTrue -> v1
    | BFalse -> v0
    | BIf (v, h, l) ->
      let var_vertex = G.V.create (atom_label v)
      and true_vertex = visit h
      and false_vertex = visit l in
      G.add_edge_e
        graph
        (G.E.create
           var_vertex
           E.{ label = true; complement = false; selected = false }
           true_vertex);
      G.add_edge_e
        graph
        (G.E.create
           var_vertex
           E.{ label = false; complement = false; selected = false }
           false_vertex);
      var_vertex
  in
  let _ = visit guard in
  graph
;;
