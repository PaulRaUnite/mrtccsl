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

  let state_numeric_now_bool ~now:_ = function
    | BStateVar _ -> lv0
    | BInputVar _ -> lv2
    | RatVarMarker _ -> lv3
    | IntVarMarker _ -> lv3
    | IntComp _ -> lv0
    | RatComp _ -> lv1
  ;;

  let state_bool_now_numeric ~now = function
    | BStateVar _ -> lv0
    | BInputVar _ -> lv1
    | RatComp (RInputVar _, _, RConst _) -> lv3
    | RatComp (RConst _, _, RInputVar _) -> lv3
    | IntComp (IInputVar _, _, IConst _) -> lv3
    | IntComp (IConst _, _, IInputVar _) -> lv3
    | RatVarMarker _ -> lv2
    | IntVarMarker _ -> lv2
    | atom -> fold_bool_atom (with_max lv0) (with_max lv3 ~except:(now, lv2)) lv0 atom
  ;;

  module LvIndMap = Map.Make (struct
      type t = Level.t * int [@@deriving compare]
    end)

  module LvMap = Map.Make (Level)
end

type ('sv, 'iv) t =
  { now : 'iv
  ; atoms : ('sv, 'iv) bool_atom Dynarray.t
  ; guard : Bdd.t
  ; assignments : ('sv, 'iv) assignment list
  ; threshold1 : int
  ; threshold2 : int
  }

(** Records evaluations of all Boolean atoms in a diagram, if it is fully evaluable from the input values. Assumes consistent index with the target diagram. *)
type atom_satisfaction_index = bool option Dynarray.t

let make_satisfaction_index state inputs atoms : atom_satisfaction_index =
  Dynarray.map
    (fun atom ->
       try Some (Full.eval_bool_atom state inputs atom) with
       (* we suppress any errors related to the computation, as some inputs can only be deduced in a path, i.e. do not have definitive solution in an atom *)
       | _ -> None)
    atoms
;;

module V = struct
  type t =
    | AtomNode of
        { name : string
        ; satisfied : bool option
        }
    | Constraint of string
  [@@deriving show]
end

module E = struct
  let compare_bool = Bool.compare

  type t =
    | AtomDecisionEdge of
        { label : bool
        ; selected : bool
        }
    | RefTrackingEdge
  [@@deriving compare, show]

  let default = RefTrackingEdge
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
      | AtomNode node ->
        (match node.name with
         | "0" | "1" -> [ `Label node.name; `Shape `Box ]
         | _ ->
           (match node.satisfied with
            | Some satisfied ->
              [ `Label node.name
              ; (if satisfied then `Color 0x00ff00 else `Color 0xff0000)
              ; `Style `Bold
              ]
            | None -> [ `Label node.name ]))
      | Constraint s -> [ `Label s; `Shape `Box; `Color 0xff00ff ]
    ;;

    let default_edge_attributes _ = []

    let edge_attributes e =
      match G.E.label e with
      | AtomDecisionEdge label ->
        [ `Label (string_of_bool label.label)
        ; `Style (if label.label then `Solid else `Dashed)
        ; `Color (if label.selected then 0xff0000 else 0)
        ]
      | RefTrackingEdge -> [ `Arrowhead `Normal; `Color 0xff00ff ]
    ;;

    (* TODO: add more colors, PointerEdge is a dumb name too *)

    let get_subgraph _ = None
  end)

let to_dot graph = Dot.output_graph stdout graph

type bool_var = int

type 'a b =
  | BFalse
  | BTrue
  | BIf of bool_var * 'a * 'a

let[@inline always] inspect bdd =
  if Bdd.is_true bdd
  then BTrue
  else if Bdd.is_false bdd
  then BFalse
  else BIf (Bdd.root_var bdd, Bdd.high_part bdd, Bdd.low_part bdd)
;;

let to_graph
      ?(cstr_index : atom_index option)
      ?(atom_index : atom_satisfaction_index option)
      atoms
      guard
  =
  let atom_index_to_satisfaction =
    Option.map_or ~default:(fun _ -> None) Dynarray.get atom_index
  in
  let atom_to_string a =
    Format.asprintf "%a" (PP.bool_atom Format.pp_print_string Format.pp_print_string) a
  in
  let labels = Dynarray.map atom_to_string atoms in
  let local_atom_index = Hashtbl.create 16 in
  let atom_label i = Dynarray.get labels i in
  let index = Hashtbl.create 48 in
  let graph = G.create () in
  let v1 = G.V.create (AtomNode { name = "1"; satisfied = None }) in
  let v0 = G.V.create (AtomNode { name = "0"; satisfied = None }) in
  let rec visit bdd =
    match inspect bdd with
    | BTrue -> v1
    | BFalse -> v0
    | BIf (v, h, l) ->
      (match Hashtbl.find_opt index (v, h, l) with
       | Some v -> v
       | None ->
         let label = atom_label v in
         let var_vertex =
           G.V.create
             (AtomNode { name = label; satisfied = atom_index_to_satisfaction v })
         in
         G.add_vertex graph var_vertex;
         let true_vertex = visit h
         and false_vertex = visit l in
         Hashtbl.add index (v, h, l) var_vertex;
         Hashtbl.entry ~default:[] (List.cons var_vertex) label local_atom_index;
         G.add_edge_e
           graph
           (G.E.create
              var_vertex
              (E.AtomDecisionEdge { label = true; selected = false })
              true_vertex);
         G.add_edge_e
           graph
           (G.E.create
              var_vertex
              (E.AtomDecisionEdge { label = false; selected = false })
              false_vertex);
         var_vertex)
  in
  G.add_vertex graph @@ visit guard;
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
              G.add_edge_e graph (G.E.create source RefTrackingEdge target)))
         index)
    cstr_index;
  (* Printf.printf "V: %i, E: %i\n" (G.nb_vertex graph) (G.nb_edges graph);
  G.iter_edges_e
    (fun e ->
       let s = G.V.label @@ G.E.src e
       and d = G.V.label @@ G.E.dst e
       and l = G.E.label e in
       Printf.printf "%s -- %s -> %s\n" (V.show s) (E.show l) (V.show d))
    graph; *)
  graph
;;

(* 
module Bdd2 = struct
  let file = open_out "./debug/dots.md"
  let diagrams = Dynarray.of_list [ Bdd.dfalse (); Bdd.dtrue () ]

  type t = Bdd.t * int

  let dfalse () =
    let f = Bdd.dfalse () in
    f, 0
  ;;

  let dtrue () =
    let t = Bdd.dtrue () in
    t, 1
  ;;

  let get (x, _) atoms =
    Dynarray.iteri
      (fun i d ->
         (* Printf.printf "diagram: %i\nis_true: %b\n" i (Bdd.is_true d); *)
         let f = open_out (Printf.sprintf "./debug/%i.dot" i) in
         Dot.output_graph f (to_graph atoms d);
         close_out f)
      diagrams;
    Dynarray.clear diagrams;
    Dynarray.append_list diagrams [ Bdd.dfalse (); Bdd.dtrue () ];
    x
  ;;

  let dnot (x, x_id) : t =
    let res = Bdd.dnot x in
    let id = Dynarray.length diagrams in
    Dynarray.add_last diagrams res;
    Printf.fprintf file "- [%i](./%i.dot) := NOT [%i](./%i.dot)\n" id id x_id x_id;
    res, id
  ;;

  let dand (x, x_id) (y, y_id) =
    let res = Bdd.dand x y in
    let id = Dynarray.length diagrams in
    Dynarray.add_last diagrams res;
    Printf.fprintf
      file
      "- [%i](./%i.dot) := [%i](./%i.dot) && [%i](%i.dot)\n"
      id
      id
      x_id
      x_id
      y_id
      y_id;
    res, id
  ;;

  let dor (x, x_id) (y, y_id) =
    if Bdd.is_false x
    then y, y_id
    else if Bdd.is_false y
    then x, x_id
    else (
      let res = Bdd.dor x y in
      let id = Dynarray.length diagrams in
      Dynarray.add_last diagrams res;
      Printf.fprintf
        file
        "- [%i](./%i.dot) := [%i](./%i.dot) || [%i](%i.dot)\n"
        id
        id
        x_id
        x_id
        y_id
        y_id;
      res, id)
  ;;

  let eq (x, x_id) (y, y_id) =
    let res = Bdd.eq x y in
    let id = Dynarray.length diagrams in
    Dynarray.add_last diagrams res;
    Printf.fprintf
      file
      "- [%i](./%i.dot) := [%i](./%i.dot) == [%i](%i.dot)\n"
      id
      id
      x_id
      x_id
      y_id
      y_id;
    res, id
  ;;

  let ite (x, x_id) (y, y_id) (z, z_id) =
    let res = Bdd.ite x y z in
    let id = Dynarray.length diagrams in
    Dynarray.add_last diagrams res;
    Printf.fprintf
      file
      "- [%i](./%i.dot) := if [%i](./%i.dot) then [%i](%i.dot) else [%i](%i.dot)\n"
      id
      id
      x_id
      x_id
      y_id
      y_id
      z_id
      z_id;
    res, id
  ;;

  let idy v : t =
    let res = Bdd.idy v in
    let id = Dynarray.length diagrams in
    Dynarray.add_last diagrams res;
    Printf.fprintf file "- [%i](./%i.dot) := VAR %i \n" id id v;
    res, id
  ;;
end *)

let rec bool_expr_to_bdd
  =
  (* let module Bdd = Bdd2 in *)
  function
  | BConst c -> if c then Bdd.dtrue () else Bdd.dfalse ()
  | BAtom a -> Bdd.idy a
  | BNot e ->
    let e = bool_expr_to_bdd e in
    Bdd.dnot e
  | BAnd exprs ->
    let exprs = List.map bool_expr_to_bdd exprs in
    List.fold_left Bdd.dand (Bdd.dtrue ()) exprs
  | BOr exprs ->
    let exprs = List.map bool_expr_to_bdd exprs in
    List.fold_left Bdd.dor (Bdd.dfalse ()) exprs
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

module AtomIndex = Map.Make (struct
    type t = (string, string) bool_atom

    let compare = compare_bool_atom String.compare String.compare
  end)

let of_machine ~order now { guard; assignments; invariant = _ } : _ t =
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
      (fun lv map (bool_atoms, remap, firsts) ->
         let first_i = Dynarray.length bool_atoms in
         let firsts = LvMap.add lv first_i firsts in
         for _ = 1 to AtomIndex.cardinal map do
           Dynarray.add_last bool_atoms (BStateVar "dummy")
         done;
         let remap =
           AtomIndex.fold
             (fun atom i remap ->
                let index = first_i + i in
                Dynarray.set bool_atoms index atom;
                let remap = Order.LvIndMap.add (lv, i) index remap in
                remap)
             map
             remap
         in
         bool_atoms, remap, firsts)
      !index
      (Dynarray.create (), Order.LvIndMap.empty, LvMap.empty)
  in
  let guard = map_bool_expr (fun k -> LvIndMap.find k remap) guard in
  let guard = bool_expr_to_bdd guard in
  (* let guard = bool_expr_to_bdd guard in *)
  { now
  ; atoms = bool_atoms
  ; guard
  ; assignments
  ; threshold1 =
      Option.unwrap
        ~expect:"Level 1 or 2 has to be present in a diagram"
        (Option.bind_or (LvMap.find_opt lv1 first) (fun () -> LvMap.find_opt lv2 first))
  ; threshold2 =
      Option.value
        ~default:(Dynarray.length bool_atoms)
        (Option.bind_or (LvMap.find_opt lv2 first) (fun () -> LvMap.find_opt lv3 first))
  }
;;

open Aux

type ('sv, 'iv) acc_repr = ('sv, 'iv) t

(** Makes a BDD diagram out of machine definition. Assumes that the rational numerical comparisons arranged such that the  *)
let acceptance_diagram now mach index : _ acc_repr * atom_index =
  of_machine ~order:Order.state_bool_now_numeric now mach, index
;;

(* TODO: refactor out and probably use in the native backend too *)
type 'n num_generator =
  { mutable value : 'n
  ; update : 'n num_generator -> unit
  }

type 'n generators = 'n num_generator VarMap.t

let get_value generators var = (VarMap.find var generators).value

let update_value generators var =
  let gen = VarMap.find var generators in
  gen.update gen
;;

let make_gen zero rvs =
  let update record = record.value <- rvs () in
  let gen = { value = zero; update } in
  update gen;
  gen
;;

type ('sv, 'iv) sim_repr =
  { diagram : ('sv, 'iv) t
  ; int_gens : int generators
  ; rat_gens : Common.Number.Rational.t generators
  ; clocks : 'iv array
  }

let simulation_diagram now machine clocks index =
  let Def.{ guard; _ } = machine in
  (* "at least some clock has to tick" *)
  let non_empty_solution_cond = BOr (List.map (fun c -> BAtom (BInputVar c)) clocks) in
  let guard = BAnd [ guard; non_empty_solution_cond ] in
  let diagram =
    of_machine ~order:Order.state_numeric_now_bool now { machine with guard }
  in
  let atoms =
    (* rewrite the atoms such that the now variable appears *)
    Dynarray.map
      (function
        | RatComp (l, rel, r) -> Rewrite.isolate String.compare now l rel r
        | other -> other)
      diagram.atoms
  in
  let index =
    Hashtbl.map_v
      (List.map (function
         | RatComp (l, rel, r) -> Def.Rewrite.isolate String.compare now l rel r
         | other -> other))
      index
  in
  { diagram with atoms }, index
;;

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
        let result = Full.eval_bool_atom state num_inputs atom in
        factor_out_state_numerical
          state
          num_inputs
          threshhold
          atoms
          (if result then h else l))
;;

module VarMap = struct
  include Map.Make (String)

  module Label = struct
    module E = String

    type nonrec t = bool t
    type elt = E.t

    let mem e map = value ~default:false e map
    let to_iter map = to_iter map |> Iter.map fst
    let of_iter iter = iter |> Iter.map (fun e -> e, true) |> Iter.to_list |> of_list
    let singleton e = VarMap.singleton e true
  end
end

(** Assigns random values to free clocks. *)
let random_not_assigned clocks clock_assignments =
  Array.fold_left
    (fun asgn c -> VarMap.entry_mut ~default:Random.bool Fun.id c asgn)
    clock_assignments
    clocks
;;

module A (I : Common.Interval.I) = struct
  include I

  let iterpret_relation ~flip rel expr prev_cond =
    let rel = if flip then Common.Expr.flip rel else rel in
    inter prev_cond (of_rel rel expr)
  ;;

  let choose_branch ~flip var (rel : num_rel) value old_conds =
    let rel = if flip then Common.Expr.flip rel else (rel :> Common.Expr.num_rel) in
    let positive = of_rel rel value
    and negative = of_rel (Common.Expr.invert rel) value in
    let cond = VarMap.value ~default:inf var old_conds in
    let p_comb = inter positive cond
    and n_comb = inter negative cond in
    let with_value v = VarMap.add var v old_conds in
    ( (if is_empty p_comb then None else Some (with_value p_comb))
    , if is_empty n_comb then None else Some (with_value n_comb) )
  ;;

  let pos_neg ~flip (rel : num_rel) value old_cond =
    let rel = if flip then Common.Expr.flip rel else (rel :> Common.Expr.num_rel) in
    let positive = of_rel rel value
    and negative = of_rel (Common.Expr.invert rel) value in
    let p_comb = inter positive old_cond
    and n_comb = inter negative old_cond in
    ( (if is_empty p_comb then None else Some p_comb)
    , if is_empty n_comb then None else Some n_comb )
  ;;
end

module RI = A (Common.Interval.Make (Common.Number.Rational))
module NI = A (Common.Interval.Make (Common.Number.Integer))

(** @returns a solution to the diagram as a tuple [(map : c -> bool, timestamp)] *)
let rec random_label_strategy atoms clocks guard rat_updates int_updates clock_assignments
  =
  match inspect guard with
  | BFalse -> None
  | BTrue -> Some (random_not_assigned clocks clock_assignments, rat_updates, int_updates)
  | BIf (v, h, l) ->
    let atom = Dynarray.get atoms v in
    let chosen_high =
      if Bdd.is_false h then false else if Bdd.is_false l then true else Random.bool ()
    in
    let branch = if chosen_high then h else l in
    (match atom with
     | BInputVar clock ->
       let clock_assignments = VarMap.add clock chosen_high clock_assignments in
       random_label_strategy atoms clocks branch rat_updates int_updates clock_assignments
     (* rational and integer markers are assigned the lowest priority, so should appear last and the choice is deterministic *)
     | RatVarMarker var ->
       let rat_updates = if chosen_high then List.cons var rat_updates else rat_updates in
       random_label_strategy atoms clocks branch rat_updates int_updates clock_assignments
     | IntVarMarker var ->
       let int_updates = if chosen_high then List.cons var int_updates else int_updates in
       random_label_strategy atoms clocks branch rat_updates int_updates clock_assignments
     | BStateVar _ ->
       failwith
         "random_label_strategy: Boolean state variable should not appear after input"
     | RatComp _ | IntComp _ ->
       failwith
         "random_label_strategy: rational and integer comparisons should not appear")
;;

type 'v reduction =
  | Const of 'v
  | Variable of var

let rec reduce_inputs_rat_expr (state : _ state_interface) inputs now = function
  | RConst c -> Const c
  | RStateVar v -> Const (state.rational v)
  | RInputVar v -> if String.equal v now then Variable v else Const (inputs.rational v)
  | RITE _ ->
    failwith "reduce_rat_expr: if-then-else should not occur in an atom"
    (* TODO: remove this case on type level *)
  | RBinOp (l, op, r) ->
    let l = reduce_inputs_rat_expr state inputs now l
    and r = reduce_inputs_rat_expr state inputs now r in
    (match l, r with
     | Const l, Const r -> Const (Common.Number.Rational.do_op op l r)
     | _ ->
       failwith
         "reduce_rat_expr: binary operation cannot add variable and constant, both have \
          to be constant")
  | RPeekFirstQueue q -> Const (Queue.peek (state.rat_queue q))
  | RPeekLastQueue q -> Const (Queue.last (state.rat_queue q))
;;

let rec reduce_to_bool_solutions atoms bool_threshold state inputs now guard time_cond =
  match inspect guard with
  | BTrue -> [ time_cond, guard ]
  | BFalse -> []
  | BIf (v, high, low) ->
    if bool_threshold <= v
    then [ time_cond, guard ]
    else (
      let atom = Dynarray.get atoms v in
      match atom with
      | RatComp (l, rel, r) ->
        let l = reduce_inputs_rat_expr state inputs now l
        and r = reduce_inputs_rat_expr state inputs now r in
        let when_high, when_low =
          match l, r with
          | Const l, Variable _ -> RI.pos_neg ~flip:true rel l time_cond
          | Variable _, Const r -> RI.pos_neg ~flip:false rel r time_cond
          | Const l, Const r ->
            if Common.Expr.do_rel ~compare:Common.Number.Rational.compare rel l r
            then Some time_cond, None
            else None, Some time_cond
          | Variable _, Variable _ ->
            failwith
              "reduce_to_bool_solutions: variable-variable comparisons are not supported"
        in
        let high_solutions =
          match when_high with
          | Some time_cond ->
            reduce_to_bool_solutions atoms bool_threshold state inputs now high time_cond
          | None -> []
        and low_solutions =
          match when_low with
          | Some time_cond ->
            reduce_to_bool_solutions atoms bool_threshold state inputs now low time_cond
          | None -> []
        in
        List.append high_solutions low_solutions
      | IntComp _ ->
        failwith
          "reduce_to_bool_solutions: integer comparisons should be already resolved"
      | BStateVar _ ->
        failwith
          "reduce_to_bool_solutions: boolean state variables should be already applied"
      | BInputVar _ ->
        failwith
          "reduce_to_bool_solutions: input variables should be detected by threshold"
      | IntVarMarker _ | RatVarMarker _ ->
        failwith
          "reduce_to_bool_solutions: markers should not appear before the threshold")
;;

let gen_step
      bound_strategy
      ({ diagram = { now; guard; assignments; threshold1; threshold2; atoms }
       ; int_gens
       ; rat_gens
       ; clocks
       } :
        _ sim_repr)
      state
  : (state * (bool VarMap.t * Common.Number.Rational.t)) option
  =
  let state_int = state_to_interface state in
  let partial_input_int =
    { rational = get_value rat_gens
    ; integer = get_value int_gens
    ; bool =
        (fun _ -> failwith "do_step: Boolean inputs are supposed to be chosen by the ")
    }
  in
  let solution_guard =
    factor_out_state_numerical state_int partial_input_int threshold1 atoms guard
  in
  let solutions =
    reduce_to_bool_solutions
      atoms
      threshold2
      state_int
      partial_input_int
      now
      solution_guard
      RI.inf
  in
  if List.is_empty solutions
  then None
  else (
    let solutions = Array.of_list solutions in
    let bound, clock_bdd = Array.random solutions in
    let* clock_assignments, rat_updates, int_updates =
      random_label_strategy atoms clocks clock_bdd [] [] VarMap.empty
    in
    let time = bound_strategy bound in
    let input_int =
      { rational = (fun v -> if String.equal now v then time else get_value rat_gens v)
      ; integer = get_value int_gens
      ; bool = (fun v -> VarMap.find v clock_assignments)
      }
    in
    let new_state =
      Transition.apply_assignments state_int input_int default_state assignments
    in
    List.iter (update_value rat_gens) rat_updates;
    List.iter (update_value int_gens) int_updates;
    Some (new_state, (clock_assignments, time)))
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

let rec reduce_time_rat_expr (state : _ state_interface) now time = function
  | RConst c -> Const c
  | RStateVar v -> Const (state.rational v)
  | RInputVar v -> if String.equal v now then Const time else Variable v
  | RITE _ ->
    failwith "reduce_rat_expr: if-then-else should not occur in an atom"
    (* TODO: remove this case on type level *)
  | RBinOp (l, op, r) ->
    let l = reduce_time_rat_expr state now time l
    and r = reduce_time_rat_expr state now time r in
    (match l, r with
     | Const l, Const r -> Const (Common.Number.Rational.do_op op l r)
     | _ ->
       failwith
         "reduce_rat_expr: binary operation cannot add variable and constant, both have \
          to be constant")
  | RPeekFirstQueue q -> Const (Queue.peek (state.rat_queue q))
  | RPeekLastQueue q -> Const (Queue.last (state.rat_queue q))
;;

let rec reduce_int_expr (state : _ state_interface) = function
  | IConst c -> Const c
  | IStateVar v -> Const (state.integer v)
  | IInputVar v -> Variable v
  | IITE _ ->
    failwith "reduce_int_expr: if-then-else should not occur in an atom"
    (* TODO: remove this case on type level *)
  | IBinOp (l, op, r) ->
    let l = reduce_int_expr state l
    and r = reduce_int_expr state r in
    (match l, r with
     | Const l, Const r -> Const (Common.Number.Integer.do_op op l r)
     | _ ->
       failwith
         "reduce_int_expr: binary operation cannot add variable and constant, both have \
          to be constant")
  | IPeekFirstQueue q -> Const (Queue.peek (state.int_queue q))
  | IPeekLastQueue q -> Const (Queue.last (state.int_queue q))
  | IntQueueLength q -> Const (Queue.length @@ state.int_queue q)
  | RatQueueLength q -> Const (Queue.length @@ state.rat_queue q)
;;

let bdd_to_string ~var_to_string guard =
  match inspect guard with
  | BTrue -> "true"
  | BFalse -> "false"
  | BIf (v, _, _) -> var_to_string v
;;

let bdd_to_string_nested ~var_to_string guard =
  match inspect guard with
  | BTrue -> "true"
  | BFalse -> "false"
  | BIf (v, high, low) ->
    Printf.sprintf
      "if %s then \n%s\nelse\n%s"
      (var_to_string v)
      (bdd_to_string ~var_to_string high)
      (bdd_to_string ~var_to_string low)
;;

let atom_to_string atoms i =
  let atom = Dynarray.get atoms i in
  Format.asprintf "%a" (PP.bool_atom Format.pp_print_string Format.pp_print_string) atom
;;

let some_add_q q o =
  let addq z = q, z in
  let q, nq = o in
  Option.map addq q, Option.map addq nq
;;

let some_add_z z o =
  let addz q = q, z in
  let q, nq = o in
  Option.map addz q, Option.map addz nq
;;

(* TODO: maybe go back to using native equality in the constraints and use disjunctions as the domain (in a sense, it is a DFS instead of DFS) *)
(** Collects numerical relations into Q and Z polyhedras. Assumes that state and clock were already followed. *)
let rec derive_num_inputs
          now
          state
          inputs
          time
          atoms
          guard
          required_ints
          required_rats
          (old_q, old_z)
  =
  match inspect guard with
  | BTrue -> Some (old_q, old_z)
  | BFalse -> None
  | BIf (v, high, low) ->
    let atom = Dynarray.get atoms v in
    let when_high, when_low =
      match atom with
      | BStateVar _ | BInputVar _ ->
        failwith
          "derive_num_inputs: state and input Booleans are supposed to be already \
           factored out"
      | IntComp (l, rel, r) ->
        let l = reduce_int_expr state l
        and r = reduce_int_expr state r in
        (match l, r with
         | Const l, Const r ->
           let result =
             Common.Expr.do_rel ~compare:Common.Number.Integer.compare rel l r
           in
           if result then Some (old_q, old_z), None else None, Some (old_q, old_z)
         | Variable var, Const r ->
           some_add_q old_q @@ NI.choose_branch ~flip:false var rel r old_z
         | Const l, Variable var ->
           some_add_q old_q @@ NI.choose_branch ~flip:true var rel l old_z
         | Variable _, Variable _ ->
           failwith "derive_num_inputs: cannot derive from diagonal relations")
      | RatComp (l, rel, r) ->
        let l = reduce_time_rat_expr state now time l
        and r = reduce_time_rat_expr state now time r in
        (match l, r with
         | Const l, Const r ->
           let result =
             Common.Expr.do_rel ~compare:Common.Number.Rational.compare rel l r
           in
           if result then Some (old_q, old_z), None else None, Some (old_q, old_z)
         | Variable var, Const r ->
           some_add_z old_z @@ RI.choose_branch ~flip:false var rel r old_q
         | Const l, Variable var ->
           some_add_z old_z @@ RI.choose_branch ~flip:true var rel l old_q
         | Variable v1, Variable v2 ->
           failwithf
             "derive_num_inputs: cannot derive from diagonal relations, %s %s %s\n"
             v1
             (Common.Expr.string_of_num_rel rel)
             v2)
      | IntVarMarker _ | RatVarMarker _ -> Some (old_q, old_z), Some (old_q, old_z)
    in
    let check_markers choice = function
      | IntVarMarker v -> if choice then required_ints := VarMap.add v () !required_ints
      | RatVarMarker v -> if choice then required_rats := VarMap.add v () !required_rats
      | _ -> ()
    in
    let can_high = not (Bdd.is_false high)
    and can_low = not (Bdd.is_false low) in
    let when_high = if can_high then when_high else None
    and when_low = if can_low then when_low else None in
    (match when_high, when_low with
     | Some when_high, Some when_low ->
       let high_result =
         derive_num_inputs
           now
           state
           inputs
           time
           atoms
           high
           required_ints
           required_rats
           when_high
       in
       (match high_result with
        | Some result ->
          check_markers true atom;
          Some result
        | None ->
          let low_result =
            derive_num_inputs
              now
              state
              inputs
              time
              atoms
              low
              required_ints
              required_rats
              when_low
          in
          (match low_result with
           | Some result ->
             check_markers false atom;
             Some result
           | None -> None))
     | Some when_high, None ->
       check_markers true atom;
       derive_num_inputs
         now
         state
         inputs
         time
         atoms
         high
         required_ints
         required_rats
         when_high
     | None, Some when_low ->
       check_markers false atom;
       derive_num_inputs
         now
         state
         inputs
         time
         atoms
         low
         required_ints
         required_rats
         when_low
     | None, None -> None)
;;

type parameters = int VarMap.t * Common.Number.Rational.t VarMap.t

let accept_solution
      { now; atoms; guard; assignments; threshold1; threshold2 }
      state
      (clock_assignments, time)
  : (state * parameters) option
  =
  let input_int =
    { rational = (fun _ -> failwith "accept_solution: rational inputs should not be used")
    ; integer = (fun _ -> failwith "accept_solution: integer inputs should not be used")
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
  let required_ints = ref VarMap.empty
  and required_rats = ref VarMap.empty in
  let* q, z =
    derive_num_inputs
      now
      state_int
      input_int
      time
      atoms
      partial_guard
      required_ints
      required_rats
      (VarMap.empty, VarMap.empty)
  in
  let rationals =
    VarMap.merge
      (fun _ marked value ->
         match marked, value with
         | Some (), Some value -> RI.as_singleton value
         | _ -> None)
      !required_rats
      q
  in
  let integers =
    VarMap.merge
      (fun _ marked value ->
         match marked, value with
         | Some (), Some value -> NI.as_singleton value
         | _ -> None)
      !required_ints
      z
  in
  let all_sampled =
    VarMap.cardinal !required_ints = VarMap.cardinal integers
    && VarMap.cardinal !required_rats = VarMap.cardinal rationals
  in
  if all_sampled
  then (
    let all_rationals = VarMap.add now time rationals in
    let input_int =
      { integer =
          (fun v ->
            try VarMap.find v integers with
            | Not_found -> failwithf "not found: %s" v)
      ; rational =
          (fun v ->
            try VarMap.find v all_rationals with
            | Not_found -> failwithf "not found: %s" v)
      ; bool = (fun v -> VarMap.value ~default:false v clock_assignments)
      }
    in
    Some
      ( Transition.apply_assignments state_int input_int default_state assignments
      , (integers, rationals) ))
  else None
;;
