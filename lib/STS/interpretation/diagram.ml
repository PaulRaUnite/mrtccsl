(** ROBDD-based backend for the symbolic transition systems. *)
open Common.Prelude

open Def

module Order = struct
  open Ppx_compare_lib.Builtin

  module Level = struct
    type t = Level of int [@@deriving compare]
  end

  open Level

  let lv3 = Level 3
  let lv2 = Level 2
  let lv1 = Level 1
  let lv0 = Level 0
  let min (Level x) (Level y) = Level (Int.min x y)
  let max (Level x) (Level y) = Level (Int.max x y)

  let with_max ?except lv x v =
    let lv =
      match except with
      | Some (ext, lv) when ext = v -> lv
      | _ -> lv
    in
    max x lv
  ;;

  let with_min ?except lv x v =
    let lv =
      match except with
      | Some (ext, lv) when ext = v -> lv
      | _ -> lv
    in
    min x lv
  ;;

  let state_input_now ~now atom =
    fold_bool_atom (with_max lv0) (with_max lv1 ~except:(now, lv2)) lv0 atom
  ;;

  let state_numeric_bool_now ~now = function
    | BStateVar _ -> lv0
    | BInputVar _ -> lv2
    | atom -> fold_bool_atom (with_max lv0) (with_max lv1 ~except:(now, lv3)) lv0 atom
  ;;

  let state_bool_now_numeric ~now:_ = function
    | BStateVar _ -> lv0
    | BInputVar _ -> lv1
    | atom -> fold_bool_atom (with_max lv0) (with_max lv2) lv0 atom
  ;;

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
    List.fold_left Bdd.dor (Bdd.dfalse ()) es
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
  ; threshold1 : int
  ; threshold2 : int
  }

module AtomIndex = Map.Make (struct
    type t = (string, string) bool_atom

    let compare = compare_bool_atom String.compare String.compare
  end)

let of_machine ~order now { guard; assignments; invariant = _ } : _ t =
  (* print_endline
  @@ Sexplib0.Sexp.to_string_hum
  @@ sexp_of_bool_expr (sexp_of_bool_atom String.sexp_of_t String.sexp_of_t) guard; *)
  let open Order in
  let index = ref LvMap.empty in
  let assign_temp_id expr =
    let lv = order ~now expr in
    let map = LvMap.value ~default:AtomIndex.empty lv !index in
    let i = AtomIndex.value ~default:(AtomIndex.cardinal map) expr map in
    let map = AtomIndex.add expr i map in
    index := LvMap.add lv map !index;
    lv, i
  in
  let guard = map_bool_expr assign_temp_id guard in
  let bool_atoms, remap, first =
    LvMap.fold
      (fun lv map (bool_atoms, remap, first) ->
         let remap, first =
           AtomIndex.fold
             (fun atom i (remap, first) ->
                Dynarray.add_last bool_atoms atom;
                let index = Dynarray.length bool_atoms - 1 in
                let remap = Order.LvIndMap.add (lv, i) index remap
                and first = LvMap.entry ~default:index Fun.id lv first in
                remap, first)
             map
             (remap, first)
         in
         bool_atoms, remap, first)
      !index
      (Dynarray.create (), Order.LvIndMap.empty, LvMap.empty)
  in
  let guard = map_bool_expr (fun k -> LvIndMap.find k remap) guard in
  let guard = bool_expr_to_bdd guard in
  { now
  ; atoms = bool_atoms
  ; guard
  ; assignments
  ; threshold1 =
      Option.unwrap
        ~expect:"Level 1 or 2 has to be present in a diagram"
        (Option.bind_or (LvMap.find_opt lv1 first) (fun () -> LvMap.find_opt lv2 first))
  ; threshold2 =
      Option.unwrap
        ~expect:"Level 2 or 3 has to be present in a diagram"
        (Option.bind_or (LvMap.find_opt lv2 first) (fun () -> LvMap.find_opt lv3 first))
  }
;;

module V = struct
  type t =
    | BDDNode of string
    | Constraint of string
end

module E = struct
  let compare_bool = Bool.compare

  type t =
    | BDDEdge of
        { complement : bool
        ; label : bool
        ; selected : bool
        }
    | PointerEdge
  [@@deriving compare]

  let default = PointerEdge
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
      | BDDNode node_name ->
        (match node_name with
         | "0" | "1" -> [ `Label node_name; `Shape `Box ]
         | _ -> [ `Label node_name ])
      | Constraint s -> [ `Label s; `Shape `Box; `Color 0xff00ff ]
    ;;

    let default_edge_attributes _ = []

    let edge_attributes e =
      match G.E.label e with
      | BDDEdge label ->
        [ `Label (string_of_bool label.label)
        ; `Arrowhead (if label.complement then `Dot else `Normal)
        ; `Color (if label.selected then 0xff0000 else 0)
        ]
      | PointerEdge -> [ `Arrowhead `Normal; `Color 0xff00ff ]
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

let[@inline always] inspect bdd =
  if Bdd.is_true bdd
  then BTrue
  else if Bdd.is_false bdd
  then BFalse
  else BIf (Bdd.root_var bdd, Bdd.high_part bdd, Bdd.low_part bdd)
;;

open Aux

(** @returns BDD that was specialized by the state and input variables *)
let rec factor_out_state_numerical
          (state : string state_interface)
          num_inputs
          threshhold
          atoms
          guard
  =
  match inspect guard with
  | BFalse | BTrue -> guard
  | BIf (v, h, l) ->
    if threshhold <= v
    then guard
    else (
      let atom = Dynarray.get atoms v in
      match atom with
      | BInputVar _ -> guard
      | _ ->
        Format.printf
          "%a\n"
          (PP.bool_atom Format.pp_print_string Format.pp_print_string)
          atom;
        Format.printf "what...\n";
        Format.print_flush ();
        let result = Full.eval_bool_atom state num_inputs atom in
        factor_out_state_numerical
          state
          num_inputs
          threshhold
          atoms
          (if result then h else l))
;;

module VarMap = Map.Make (String)

(** Assigns random values to free clocks. *)
let random_not_assigned clocks clock_assignments =
  Array.fold_left
    (fun asgn c -> VarMap.entry_mut ~default:Random.bool Fun.id c asgn)
    clock_assignments
    clocks
;;

module I = Common.Interval.Make (Common.Number.Rational)

let iterpret_relation ~invert rel expr prev_cond =
  let rel = if invert then Common.Expr.invert rel else rel in
  I.inter prev_cond (I.of_rel rel expr)
;;

(** @returns a solution to the diagram as a tuple [(map : c -> bool, timestamp)] *)
let rec random_label_strategy
          state
          inputs
          delay_strategy
          now
          atoms
          clocks
          guard
          clock_assignments
          delay_interval
  =
  match inspect guard with
  | BFalse -> None
  | BTrue ->
    Some (random_not_assigned clocks clock_assignments, delay_strategy delay_interval)
  | BIf (v, h, l) ->
    let atom = Dynarray.get atoms v in
    let chosen_high =
      if Bdd.is_false h then false else if Bdd.is_false l then true else Random.bool ()
    in
    let branch = if chosen_high then h else l in
    let clock_assignments, delay_interval =
      match atom with
      | BStateVar _ ->
        failwith
          "random_label_strategy: Boolean state variable should not appear after input"
      | BInputVar clock ->
        let clock_assignments = VarMap.add clock chosen_high clock_assignments in
        clock_assignments, delay_interval
      | IntComp _ ->
        failwith
          "random_label_strategy: integer-related comparison should not occur during \
           strategy resolution"
      | RatComp (RInputVar maybe_now, rel, expr) when String.equal maybe_now now ->
        let delay_interval =
          iterpret_relation
            ~invert:(not chosen_high)
            (rel :> Common.Expr.num_rel)
            (Full.eval_rational state inputs expr)
            delay_interval
        in
        clock_assignments, delay_interval
      | RatComp (expr, rel, RInputVar maybe_now) when String.equal maybe_now now ->
        let delay_interval =
          iterpret_relation
            ~invert:(not chosen_high)
            (Common.Expr.flip rel)
            (Full.eval_rational state inputs expr)
            delay_interval
        in
        clock_assignments, delay_interval
      | _ -> failwith "unreachable"
    in
    random_label_strategy
      state
      inputs
      delay_strategy
      now
      atoms
      clocks
      branch
      clock_assignments
      delay_interval
;;

(** Follows Boolean variables as assigned in the [clock_values].
Assumes that the state variables were already followed. *)
let rec factor_out_boolean_inputs atoms clock_values threshhold guard =
  match inspect guard with
  | BTrue | BFalse -> guard
  | BIf (v, h, l) ->
    if threshhold <= v
    then guard
    else (
      let atom = Dynarray.get atoms v in
      match atom with
      | BInputVar v ->
        let branch = if clock_values.bool v then h else l in
        factor_out_boolean_inputs atoms clock_values threshhold branch
      | BStateVar _ ->
        failwith
          "factor_out_boolean_inputs: state variable should not be present at diagram \
           depth"
      | _ -> guard)
;;

module IdentQ = Vpl.UserInterface.Lift_Ident (String)
module IdentZ = Vpl.UserInterface.Lift_Ident (String)

module TermQ = struct
  type t = Vpl.WrapperTraductors.Interface(Vpl.Domains.UncertifiedQ.Coeff).Term.t

  let to_term t = t
  let of_term t = t
end

module TermZ = struct
  type t = Vpl.WrapperTraductors.Interface(Vpl.Domains.UncertifiedZ.Coeff).Term.t

  let to_term t = t
  let of_term t = t
end

module DZ = struct
  include Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedZ) (IdentZ) (TermZ)
end

module DQ = struct
  include Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedQ) (IdentQ) (TermQ)

  module Coeff = struct
    include Coeff

    let of_rational x =
      let num, den = Common.Number.Rational.to_int2 x in
      Q.make (Z.of_int num) (Z.of_int den)
    ;;

    let to_rational x =
      Common.Number.Rational.from_pair Q.(Z.to_int x.num, Z.to_int x.den)
    ;;
  end
end

type num_sol = DQ.t * DZ.t

let convert_rel_to_vpl = function
  | `Less -> Vpl.Cstr_type.LT
  | `LessEq -> Vpl.Cstr_type.LE
;;

let intcomp_to_polyhedra (state : _ state_interface) inputs l rel r : DZ.Cond.t =
  let rec interpret_int_expr = function
    | IConst c -> DZ.Term.Cte (DZ.Coeff.of_int c)
    | IStateVar var -> DZ.Term.Cte (DZ.Coeff.of_int (state.integer var))
    | IInputVar var ->
      print_endline var;
      print_endline (Vpl.Var.to_string @@ IdentZ.toVar var);
      DZ.Term.Var (IdentZ.toVar var)
    | IBinOp (e1, op, e2) ->
      let e1 = interpret_int_expr e1
      and e2 = interpret_int_expr e2 in
      (match op with
       | `Div -> DZ.Term.Div (e1, e2)
       | `Add -> DZ.Term.Add (e1, e2)
       | `Sub -> DZ.Term.Add (e1, DZ.Term.Opp e2)
       | `Mul -> DZ.Term.Mul (e1, e2))
    | IPeekFirstQueue q -> DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.peek @@ state.int_queue q)
    | IPeekLastQueue q -> DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.last @@ state.int_queue q)
    | IntQueueLength q ->
      DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.length @@ state.int_queue q)
    | RatQueueLength q ->
      DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.length @@ state.rat_queue q)
    | IITE { cond; if_true; if_false } ->
      if Full.eval_bool state inputs cond
      then interpret_int_expr if_true
      else interpret_int_expr if_false
  in
  let l = interpret_int_expr l
  and r = interpret_int_expr r
  and rel = convert_rel_to_vpl rel in
  DZ.Cond.Atom (l, rel, r)
;;

let ratcomp_to_polyhedra (state : _ state_interface) inputs now time l rel r : DQ.Cond.t =
  let rec interpret_rat_expr = function
    | RConst c -> DQ.Term.Cte (DQ.Coeff.of_rational c)
    | RStateVar var -> DQ.Term.Cte (DQ.Coeff.of_rational (state.rational var))
    | RInputVar var ->
      if String.equal var now
      then DQ.Term.Cte (DQ.Coeff.of_rational time)
      else DQ.Term.Var (IdentQ.toVar var)
    | RBinOp (e1, op, e2) ->
      let e1 = interpret_rat_expr e1
      and e2 = interpret_rat_expr e2 in
      (match op with
       | `Div -> DQ.Term.Div (e1, e2)
       | `Add -> DQ.Term.Add (e1, e2)
       | `Sub -> DQ.Term.Add (e1, DQ.Term.Opp e2)
       | `Mul -> DQ.Term.Mul (e1, e2))
    | RPeekFirstQueue q ->
      DQ.Term.Cte (DQ.Coeff.of_rational @@ Queue.peek @@ state.rat_queue q)
    | RPeekLastQueue q ->
      DQ.Term.Cte (DQ.Coeff.of_rational @@ Queue.last @@ state.rat_queue q)
    | RITE { cond; if_true; if_false } ->
      if Full.eval_bool state inputs cond
      then interpret_rat_expr if_true
      else interpret_rat_expr if_false
  in
  let l = interpret_rat_expr l
  and r = interpret_rat_expr r
  and rel = convert_rel_to_vpl rel in
  DQ.Cond.Atom (l, rel, r)
;;

(** Collects numerical relations into Q and Z polyhedras. Assumes that state and clock were already followed. *)
let rec derive_num_inputs now state inputs time atoms guard (old_q, old_z) =
  match inspect guard with
  | BTrue -> old_q, old_z
  | BFalse -> DQ.bottom, DZ.bottom
  | BIf (v, high, low) ->
    (* Because we interpret CCSL, the high and low branches after applying should never be true at the same time. *)
    let atom = Dynarray.get atoms v in
    (match atom with
     | BStateVar _ | BInputVar _ ->
       failwith
         "derive_num_inputs: state and input Booleans are supposed to be already met"
     | IntComp (l, rel, r) ->
       let cond = intcomp_to_polyhedra state inputs l rel r in
       let z = DZ.assume (DZ.of_cond cond) old_z in
       let inv_z = DZ.assume (DZ.of_cond (DZ.Cond.Not cond)) old_z in
       (match DZ.is_bottom z, DZ.is_bottom inv_z with
        | true, false -> derive_num_inputs now state inputs time atoms low (old_q, inv_z)
        | false, true -> derive_num_inputs now state inputs time atoms high (old_q, z)
        | false, false ->
          if Bdd.is_false high
          then derive_num_inputs now state inputs time atoms low (old_q, inv_z)
          else if Bdd.is_false low
          then derive_num_inputs now state inputs time atoms high (old_q, z)
          else
            failwith
              "derive_num_inputs: there should not be a choice in the diagram for \
               rational values"
        | true, true -> DQ.bottom, DZ.bottom)
     | RatComp (l, rel, r) ->
       let cond = ratcomp_to_polyhedra state inputs now time l rel r in
       let q = DQ.assume (DQ.of_cond cond) old_q in
       let inv_q = DQ.assume (DQ.of_cond (DQ.Cond.Not cond)) old_q in
       (match DQ.is_bottom q, DQ.is_bottom inv_q with
        | true, false -> derive_num_inputs now state inputs time atoms low (inv_q, old_z)
        | false, true -> derive_num_inputs now state inputs time atoms high (q, old_z)
        | false, false ->
          if Bdd.is_false high
          then derive_num_inputs now state inputs time atoms low (inv_q, old_z)
          else if Bdd.is_false low
          then derive_num_inputs now state inputs time atoms high (q, old_z)
          else
            failwith
              "derive_num_inputs: there should not be a choice in the diagram for \
               rational values"
        | true, true -> DQ.bottom, DZ.bottom))
;;

let accept_solution
      { now; atoms; guard; assignments; threshold1; threshold2 }
      state
      (clock_assignments, time)
  =
  let input_int =
    { rational =
        (fun _ -> failwith "accept_solution: rational inputs should not be accessed")
    ; integer =
        (fun _ -> failwith "accept_solution: integer inputs should not be accessed")
    ; bool = (fun v -> VarMap.value ~default:false v clock_assignments)
    }
  in
  let state_int = state_to_interface state in
  let partial_guard =
    factor_out_state_numerical state_int input_int threshold1 atoms guard
  in
  let partial_guard =
    factor_out_boolean_inputs atoms input_int threshold2 partial_guard
  in
  let q, z =
    derive_num_inputs now state_int input_int time atoms partial_guard (DQ.top, DZ.top)
  in
  print_endline (DQ.to_string String.to_string q);
  print_endline (DZ.to_string String.to_string z);
  let* q, z =
    try Some (DQ.spawn q, DZ.spawn z) with
    | Failure s ->
      print_endline s;
      None
  in
  let rationals =
    q
    |> Vpl.Vector.Rat.toList
    |> List.to_seq
    |> Seq.map (fun (var, value) -> IdentQ.ofVar var, DQ.Coeff.to_rational value)
    |> VarMap.of_seq
  in
  let rationals = VarMap.add now time rationals in
  print_endline (Vpl.Vector.Rat.to_string Vpl.Var.to_string z);
  IdentZ.print_maps ();
  z
  |> Vpl.Vector.Rat.toList
  |> List.to_seq
  |> Seq.iter (fun (var, _) -> Printf.printf "unknown var: %s" (Vpl.Var.to_string var));
  let integers =
    z
    |> Vpl.Vector.Rat.toList
    |> List.to_seq
    |> Seq.map (fun (var, value) ->
      Printf.printf "unknown var: %s" (Vpl.Var.to_string var);
      IdentZ.ofVar var, Option.get (DQ.Coeff.to_int value Vpl.Scalar_type.Up))
    |> VarMap.of_seq
  in
  let input_int =
    { integer =
        (fun v ->
          try VarMap.find v integers with
          | Not_found -> failwithf "not found: %s" v
          | _ -> failwith "something")
    ; rational =
        (fun v ->
          try VarMap.find v rationals with
          | Not_found -> failwithf "not found: %s" v
          | _ -> failwith "something else")
    ; bool = (fun v -> VarMap.value ~default:false v clock_assignments)
    }
  in
  print_endline "is it in the assignments?";
  Some (Transition.apply_assignments state_int input_int state assignments)
;;

let to_graph ?(cstr_index : atom_index option) { guard; atoms; _ } =
  let atom_to_string a =
    Format.asprintf "%a" (PP.bool_atom Format.pp_print_string Format.pp_print_string) a
  in
  let labels = Dynarray.map atom_to_string atoms in
  let local_atom_index = Hashtbl.create 16 in
  let atom_label i = Dynarray.get labels i in
  let index = Hashtbl.create 48 in
  let graph = G.create () in
  let v1 = G.V.create (BDDNode "1") in
  let v0 = G.V.create (BDDNode "0") in
  let rec visit bdd =
    match inspect bdd with
    | BTrue -> v1
    | BFalse -> v0
    | BIf (v, h, l) ->
      (match Hashtbl.find_opt index (v, h, l) with
       | Some v -> v
       | None ->
         let label = atom_label v in
         let var_vertex = G.V.create (BDDNode label)
         and true_vertex = visit h
         and false_vertex = visit l in
         Hashtbl.add index (v, h, l) var_vertex;
         Hashtbl.entry ~default:[] (List.cons var_vertex) label local_atom_index;
         G.add_edge_e
           graph
           (G.E.create
              var_vertex
              (E.BDDEdge { label = true; complement = false; selected = false })
              true_vertex);
         G.add_edge_e
           graph
           (G.E.create
              var_vertex
              (E.BDDEdge { label = false; complement = false; selected = false })
              false_vertex);
         var_vertex)
  in
  let _ = visit guard in
  Option.iter
    (fun index ->
       Hashtbl.iter
         (fun k v ->
            let source = G.V.create (Constraint k) in
            G.add_vertex graph source;
            v
            |> List.to_seq
            |> Seq.map atom_to_string
            |> Seq.filter_map (Hashtbl.find_opt local_atom_index)
            |> Seq.map List.to_seq
            |> Seq.concat
            |> Seq.iter (fun target ->
              G.add_edge_e graph (G.E.create source PointerEdge target)))
         index)
    cstr_index;
  graph
;;
