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

  let state_bool_now_numeric ~now = function
    | BStateVar _ -> lv0
    | BInputVar _ -> lv1
    | RatComp (RInputVar _, _, RConst _) -> lv2
    | RatComp (RConst _, _, RInputVar _) -> lv2
    | IntComp (IInputVar _, _, IConst _) -> lv2
    | IntComp (IConst _, _, IInputVar _) -> lv2
    | atom -> fold_bool_atom (with_max lv0) (with_max ~except:(now, lv3) lv3) lv0 atom
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
  Format.printf
    "the guard:\n%a\n"
    (PP.bool_expr @@ PP.bool_atom Format.pp_print_string Format.pp_print_string)
    guard;
  let open Order in
  let index = ref LvMap.empty in
  let assign_temp_id expr =
    let lv = order ~now expr in
    let (Level.Level lvl_i) = lv in
    Format.printf
      "lvl: %i, %a\n"
      lvl_i
      (PP.bool_atom Format.pp_print_string Format.pp_print_string)
      expr;
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
  Format.printf "---  ---\n";
  Dynarray.iter
    (fun a ->
       Format.printf "%a\n" (PP.bool_atom Format.pp_print_string Format.pp_print_string) a)
    bool_atoms;
  Format.printf "---  ---\n";
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
      Option.value
        ~default:(Dynarray.length bool_atoms)
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

module A (I : Common.Interval.I) = struct
  include I

  let iterpret_relation ~flip rel expr prev_cond =
    let rel = if flip then Common.Expr.flip rel else rel in
    inter prev_cond (of_rel rel expr)
  ;;

  let choose_branch ~flip branch var (rel : num_rel) value old_conds =
    let rel = if flip then Common.Expr.flip rel else (rel :> Common.Expr.num_rel) in
    let positive = of_rel rel value
    and negative = of_rel (Common.Expr.invert rel) value in
    let cond = VarMap.value ~default:inf var old_conds in
    let p_comb = inter positive cond
    and n_comb = inter negative cond in
    let with_value v = VarMap.add var v old_conds in
    match is_empty p_comb, is_empty n_comb with
    | false, false ->
      print_endline "some/some";
      (match branch with
       | None -> Some (true, with_value p_comb) (* high and low are possible *)
       | Some branch ->
         if branch
         then (* high branch *)
           Some (true, with_value p_comb)
         else Some (false, with_value n_comb))
    | false, true ->
      print_endline "some/empty";
      Some (true, with_value p_comb)
    | true, false ->
      print_endline "empty/some";
      Some (false, with_value n_comb)
    | true, true ->
      print_endline "empty/empty";
      None
  ;;
end

module RI = A (Common.Interval.Make (Common.Number.Rational))
module NI = A (Common.Interval.Make (Common.Number.Integer))

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
    let inversion = if chosen_high then Fun.id else Common.Expr.invert in
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
          RI.iterpret_relation
            ~flip:false
            (inversion (rel :> Common.Expr.num_rel))
            (Full.eval_rational state inputs expr)
            delay_interval
        in
        clock_assignments, delay_interval
      | RatComp (expr, rel, RInputVar maybe_now) when String.equal maybe_now now ->
        let delay_interval =
          RI.iterpret_relation
            ~flip:true
            (inversion (Common.Expr.flip rel))
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

type 'v reduction =
  | Const of 'v
  | Variable of var

let rec reduce_rat_expr (state : _ state_interface) now time = function
  | RConst c -> Const c
  | RStateVar v -> Const (state.rational v)
  | RInputVar v -> if String.equal v now then Const time else Variable v
  | RITE _ ->
    failwith "reduce_rat_expr: if-then-else should not occur in an atom"
    (* TODO: remove this case on type level *)
  | RBinOp (l, op, r) ->
    Format.printf
      ">>> %a %s %a\n"
      (PP.rat_expr Format.pp_print_string Format.pp_print_string)
      l
      (Common.Expr.string_of_num_op op)
      (PP.rat_expr Format.pp_print_string Format.pp_print_string)
      r;
    let l = reduce_rat_expr state now time l
    and r = reduce_rat_expr state now time r in
    (match l, r with
     | Const l, Const r ->
       Const
         Common.Number.Rational.(
           match op with
           | `Add -> add l r
           | `Sub -> sub l r
           | `Mul -> mul l r
           | `Div -> div l r)
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
     | Const l, Const r ->
       Const
         Common.Number.Integer.(
           match op with
           | `Add -> add l r
           | `Sub -> sub l r
           | `Mul -> mul l r
           | `Div -> div l r)
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
  let* branch, z = o in
  Some (branch, q, z)
;;

let some_add_z z o =
  let* branch, q = o in
  Some (branch, q, z)
;;

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
  Format.printf
    "~~~ %s\n"
    (bdd_to_string_nested ~var_to_string:(atom_to_string atoms) guard);
  match inspect guard with
  | BTrue -> Some (old_q, old_z)
  | BFalse -> None
  | BIf (v, high, low) ->
    let atom = Dynarray.get atoms v in
    let branch_choice =
      if Bdd.is_false high
      then Some false
      else if Bdd.is_false low
      then Some true
      else None
    in
    let* branch, q, z =
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
           Some (result, old_q, old_z)
         | Variable var, Const r ->
           some_add_q old_q @@ NI.choose_branch ~flip:false branch_choice var rel r old_z
         | Const l, Variable var ->
           some_add_q old_q @@ NI.choose_branch ~flip:true branch_choice var rel l old_z
         | Variable _, Variable _ ->
           failwith "derive_num_inputs: cannot derive from diagonal relations")
      | RatComp (l, rel, r) ->
        let l = reduce_rat_expr state now time l
        and r = reduce_rat_expr state now time r in
        (match l, r with
         | Const l, Const r ->
           Format.printf
             "we do comparison %s %s %s\n"
             (Common.Number.Rational.to_string l)
             (Common.Expr.show_num_rel (rel :> Common.Expr.num_rel))
             (Common.Number.Rational.to_string r);
           let result =
             Common.Expr.do_rel ~compare:Common.Number.Rational.compare rel l r
           in
           Some (result, old_q, old_z)
         | Variable var, Const r ->
           some_add_z old_z @@ RI.choose_branch ~flip:false branch_choice var rel r old_q
         | Const l, Variable var ->
           some_add_z old_z @@ RI.choose_branch ~flip:true branch_choice var rel l old_q
         | Variable v1, Variable v2 ->
           failwithf
             "derive_num_inputs: cannot derive from diagonal relations, %s %s %s\n"
             v1
             (Common.Expr.string_of_num_rel rel)
             v2)
      | IntVarMarker v ->
        let choice =
          match branch_choice with
          | Some branch -> branch
          | None -> false
        in
        if choice then required_ints := VarMap.add v () !required_ints;
        Some (choice, old_q, old_z)
      | RatVarMarker v ->
        let choice =
          match branch_choice with
          | Some branch -> branch
          | None -> false
        in
        if choice then required_rats := VarMap.add v () !required_rats;
        Some (choice, old_q, old_z)
    in
    let branch = if branch then high else low in
    derive_num_inputs now state inputs time atoms branch required_ints required_rats (q, z)
;;

let accept_solution
      { now; atoms; guard; assignments; threshold1; threshold2 }
      state
      (clock_assignments, time)
  =
  print_endline @@ VarMap.to_string Fun.id Bool.to_string clock_assignments;
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
  let rationals = VarMap.filter_map (fun _ v -> RI.as_singleton v) q
  and integers = VarMap.filter_map (fun _ v -> NI.as_singleton v) z in
  print_endline @@ VarMap.to_string Fun.id Int.to_string integers;
  let rationals = VarMap.add now time rationals in
  let input_int =
    { integer =
        (fun v ->
          try VarMap.find v integers with
          | Not_found -> failwithf "not found: %s" v)
    ; rational =
        (fun v ->
          try VarMap.find v rationals with
          | Not_found -> failwithf "not found: %s" v)
    ; bool = (fun v -> VarMap.value ~default:false v clock_assignments)
    }
  in
  print_endline "is it in the assignments?";
  List.print
    (Format.printf "%a\n" (PP.assignment Format.pp_print_string Format.pp_print_string))
    assignments;
  Some (Transition.apply_assignments state_int input_int default_state assignments)
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
