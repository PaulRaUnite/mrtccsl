open Prelude
open Number
open Expr

module VarMap = struct
  include Map.Make (String)
  open Sexplib0.Sexp_conv

  let t_of_sexp conv s = list_of_sexp (pair_of_sexp string_of_sexp conv) s |> of_list
  let sexp_of_t conv m = to_list m |> sexp_of_list (sexp_of_pair sexp_of_string conv)
end

module Queue = struct
  type 'a t = 'a list

  let push e q = List.cons e q

  let pop q =
    let _, rest = List.last_partition q in
    rest
  ;;

  let peek q = Option.get (List.last q)
  let length = List.length
  let empty = []
  let last q = List.hd q
  let map = List.map
  let for_all = List.for_all

  open Sexplib0.Sexp_conv

  let t_of_sexp conv s = list_of_sexp conv s
  let sexp_of_t conv q = sexp_of_list conv q
end

open Ppx_compare_lib.Builtin
open Ppx_sexp_conv_lib.Conv

type ('b, 'v) ite =
  { cond : 'b
  ; if_true : 'v
  ; if_false : 'v
  }
[@@deriving compare, sexp]

(** Empty type. It has no constructors and so values cannot exist.
  Used to prune possibilities in polymorphic types.*)
type empty = |

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

and ('sv, 'iv) rat_expr =
  | RConst of Rational.t
  | RStateVar of 'sv
  | RInputVar of 'iv
  | RITE of (('sv, 'iv) bool_expr, ('sv, 'iv) rat_expr) ite
  | RBinOp of ('sv, 'iv) rat_expr * num_op * ('sv, 'iv) rat_expr
  | RPeekFirstQueue of 'sv
  | RPeekLastQueue of 'sv
[@@deriving compare, sexp]

type ('sv, 'iv) int_queue_expr =
  | IQVar of 'sv
  | IPushQueue of ('sv, 'iv) int_queue_expr * ('sv, 'iv) int_expr
  | IPopQueue of ('sv, 'iv) int_queue_expr
  | IDecreaseAllQueue of ('sv, 'iv) int_queue_expr
  | IIncreaseAllQueue of ('sv, 'iv) int_queue_expr
  | IQITE of (('sv, 'iv) bool_expr, ('sv, 'iv) int_queue_expr) ite
[@@deriving compare]

type ('sv, 'iv) rat_queue_expr =
  | RQVar of 'sv
  | RPushQueue of ('sv, 'iv) rat_queue_expr * ('sv, 'iv) rat_expr
  | RPopQueue of ('sv, 'iv) rat_queue_expr
  | RQITE of (('sv, 'iv) bool_expr, ('sv, 'iv) rat_queue_expr) ite
[@@deriving compare]

type ('sv, 'iv) expr =
  | BoolExpr of ('sv, 'iv) bool_expr
  | IntExpr of ('sv, 'iv) int_expr
  | RatExpr of ('sv, 'iv) rat_expr
  | IntQueueExpr of ('sv, 'iv) int_queue_expr
  | RatQueueExpr of ('sv, 'iv) rat_queue_expr
[@@deriving compare]

type ('sv, 'iv) guard = ('sv, 'iv) bool_expr [@@deriving compare]
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

(** Module of value based interpretation of the abstract machine. *)
module Interpretation = struct
  type var = string

  open Sexplib0.Sexp_conv

  (** Type of state values. *)
  type state =
    { integers : int VarMap.t (* 0 *)
    ; rationals : Rational.t VarMap.t (* -1 *)
    ; bools : bool VarMap.t (* false *)
    ; int_queues : int Queue.t VarMap.t (* [] *)
    ; rat_queues : Rational.t Queue.t VarMap.t (* [] *)
    }
  [@@deriving sexp]

  (** Default (unassigned/empty) state. *)
  let default_state =
    { rationals = VarMap.empty
    ; integers = VarMap.empty
    ; bools = VarMap.empty
    ; int_queues = VarMap.empty
    ; rat_queues = VarMap.empty
    }
  ;;

  type ('v, 'a) get_value = 'v -> 'a

  type 'v state_interface =
    { integer : ('v, int) get_value
    ; rational : ('v, Rational.t) get_value
    ; bool : ('v, bool) get_value
    ; int_queue : ('v, int Queue.t) get_value
    ; rat_queue : ('v, Rational.t Queue.t) get_value
    }

  let state_to_interface { rationals; integers; bools; int_queues; rat_queues } =
    (* TODO: need to move the default values elsewhere; logical errors, such as wrong variable names, may stay silent during execution *)
    { integer = (fun v -> VarMap.value ~default:0 v integers)
    ; rational = (fun v -> VarMap.value ~default:Rational.minus_one v rationals)
    ; bool = (fun v -> VarMap.value ~default:false v bools)
    ; int_queue = (fun v -> VarMap.value ~default:Queue.empty v int_queues)
    ; rat_queue = (fun v -> VarMap.value ~default:Queue.empty v rat_queues)
    }
  ;;

  (** Type of input values. *)
  type inputs =
    { rationals : Rational.t VarMap.t
    ; integers : int VarMap.t
    ; bools : bool VarMap.t
    }

  (* Default (unassigned/empty) inputs. *)
  let default_inputs =
    { rationals = VarMap.empty; integers = VarMap.empty; bools = VarMap.empty }
  ;;

  type ('v, 'i, 'r) input_interface =
    { integer : ('v, 'i) get_value
    ; rational : ('v, 'r) get_value
    ; bool : ('v, bool) get_value
    }

  let empty_input_interface : (empty, _, _) input_interface =
    let impossible _ = failwith "impossible situation, empty type has inhabitants" in
    { integer = impossible; rational = impossible; bool = impossible }
  ;;

  module Full = struct
    let get_iqueue state var = state.int_queue var
    let get_rqueue state var = state.rat_queue var

    let input_to_interface ({ rationals; integers; bools } : inputs) =
      { integer = (fun v -> VarMap.value ~default:0 v integers)
      ; rational = (fun v -> VarMap.value ~default:Rational.minus_one v rationals)
      ; bool = (fun v -> VarMap.value ~default:false v bools)
      }
    ;;

    (** Evaluate Boolean formula given state and input values. *)
    let rec eval_bool
              (state : 'sv state_interface)
              (inputs : ('iv, int, Rational.t) input_interface)
      : ('sv, 'iv) bool_expr -> bool
      = function
      | BConst c -> c
      | BStateVar v -> state.bool v
      | BInputVar v -> inputs.bool v
      | BNot e -> not (eval_bool state inputs e)
      | BAnd conjunctions -> List.for_all (eval_bool state inputs) conjunctions
      | BOr disjunctions -> List.exists (eval_bool state inputs) disjunctions
      | BEq (e1, e2) -> Bool.equal (eval_bool state inputs e1) (eval_bool state inputs e2)
      | BNeq (e1, e2) ->
        not (Bool.equal (eval_bool state inputs e1) (eval_bool state inputs e2))
      | BImply (e1, e2) -> (not (eval_bool state inputs e1)) || eval_bool state inputs e2
      | IntComp (e1, rel, e2) ->
        do_rel
          Int.compare
          rel
          (eval_integer state inputs e1)
          (eval_integer state inputs e2)
      | RatComp (e1, rel, e2) ->
        do_rel
          Rational.compare
          rel
          (eval_rational state inputs e1)
          (eval_rational state inputs e2)
      | BITE { cond; if_true; if_false } ->
        if eval_bool state inputs cond
        then eval_bool state inputs if_true
        else eval_bool state inputs if_false
      | IntQueuePositive q -> Queue.for_all (Integer.less_eq 0) (get_iqueue state q)

    (** Evaluate integer expression given state and input values. *)
    and eval_integer state inputs = function
      | IConst c -> c
      | IStateVar var -> state.integer var
      | IInputVar var -> inputs.integer var
      | IBinOp (e1, op, e2) ->
        let e1 = eval_integer state inputs e1
        and e2 = eval_integer state inputs e2 in
        (match op with
         | `Div -> Int.div e1 e2
         | `Add -> Int.add e1 e2
         | `Sub -> Int.sub e1 e2
         | `Mul -> Int.mul e1 e2)
      | IPeekFirstQueue qe -> Queue.peek @@ get_iqueue state qe
      | IPeekLastQueue qe -> Queue.last @@ get_iqueue state qe
      | IntQueueLength qe -> Queue.length @@ get_iqueue state qe
      | RatQueueLength qe -> Queue.length @@ get_rqueue state qe
      | IITE { cond; if_true; if_false } ->
        if eval_bool state inputs cond
        then eval_integer state inputs if_true
        else eval_integer state inputs if_false

    (** Evaluate rational expression given state and input values. *)
    and eval_rational state inputs = function
      | RConst c -> c
      | RStateVar var -> state.rational var
      | RInputVar var -> inputs.rational var
      | RBinOp (e1, op, e2) ->
        let e1 = eval_rational state inputs e1
        and e2 = eval_rational state inputs e2 in
        (match op with
         | `Div -> Rational.div e1 e2
         | `Add -> Rational.add e1 e2
         | `Sub -> Rational.sub e1 e2
         | `Mul -> Rational.mul e1 e2)
      | RPeekFirstQueue qe -> Queue.peek @@ get_rqueue state qe
      | RPeekLastQueue qe -> Queue.last @@ get_rqueue state qe
      | RITE { cond; if_true; if_false } ->
        if eval_bool state inputs cond
        then eval_rational state inputs if_true
        else eval_rational state inputs if_false
    ;;

    (** Evaluate integer queue expression given state and input values. *)
    let rec eval_int_queue state inputs = function
      | IQVar var -> get_iqueue state var
      | IPushQueue (q, e) ->
        let e = eval_integer state inputs e
        and q = eval_int_queue state inputs q in
        Queue.push e q
      | IPopQueue q ->
        let q = eval_int_queue state inputs q in
        Queue.pop q
      | IDecreaseAllQueue q -> Queue.map Int.pred (eval_int_queue state inputs q)
      | IIncreaseAllQueue q -> Queue.map Int.succ (eval_int_queue state inputs q)
      | IQITE { cond; if_true; if_false } ->
        eval_int_queue
          state
          inputs
          (if eval_bool state inputs cond then if_true else if_false)
    ;;

    (** Evaluate rational queue expression given state and input values. *)
    let rec eval_rat_queue state inputs = function
      | RQVar var -> state.rat_queue var
      | RPushQueue (q, e) ->
        let e = eval_rational state inputs e
        and q = eval_rat_queue state inputs q in
        Queue.push e q
      | RPopQueue q ->
        let q = eval_rat_queue state inputs q in
        Queue.pop q
      | RQITE { cond; if_true; if_false } ->
        eval_rat_queue
          state
          inputs
          (if eval_bool state inputs cond then if_true else if_false)
    ;;
  end

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
        integers =
          VarMap.add var (Full.eval_integer old_state inputs e) new_state.integers
      }
    | RatExpr e ->
      { new_state with
        rationals =
          VarMap.add var (Full.eval_rational old_state inputs e) new_state.rationals
      }
    | IntQueueExpr e ->
      let q = Full.eval_int_queue old_state inputs e in
      print_endline "INT QUEUE";
      print_endline var;
      print_endline Sexplib0.Sexp.(to_string @@ Queue.sexp_of_t sexp_of_int q);
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

  module Partial = struct
    module Ident = Vpl.UserInterface.Lift_Ident (String)

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
      include Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedZ) (Ident) (TermZ)

      let equal x y = leq x y && leq y x

      let not d =
        if is_bottom d
        then Seq.singleton top
        else (
          let constraints = get_cstrs d in
          constraints
          |> List.to_seq
          (* expand each linear condition into itself and its complement *)
          |> Seq.map (fun c ->
            let open Vpl.Cstr_type in
            let open Vpl.Cstr.Rat in
            match c.typ with
            | Eq ->
              let left, right = split c in
              List.to_seq [ c; left; right ]
            | _ -> Seq.cons (Vpl.Cstr.Rat.compl c) (Seq.singleton c))
            (* make combinations of all variants between original and complemented linear condition *)
          |> Seq.product_seq (* construct domain from linear inequations *)
          |> Seq.map (fun cstr -> assume (of_cond (Cond.of_cstrs (List.of_seq cstr))) top)
            (* filter out original d *)
          |> Seq.filter (not << equal d))
      ;;

      let to_string z =
        if is_bottom z
        then "bottom"
        else (
          let cstrs = get_cstrs z in
          if List.is_empty cstrs
          then "top"
          else List.to_string ~sep:" && " (Vpl.Cstr.Rat.to_string Ident.ofVar) cstrs)
      ;;
    end

    module DQ = struct
      include Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedQ) (Ident) (TermQ)

      let equal x y = leq x y && leq y x

      let not d =
        if is_bottom d
        then Seq.singleton top
        else (
          let constraints = get_cstrs d in
          constraints
          |> List.to_seq
          (* expand each linear condition into itself and its complement *)
          |> Seq.map (fun c ->
            let open Vpl.Cstr_type in
            let open Vpl.Cstr.Rat in
            match c.typ with
            | Eq ->
              let left, right = split c in
              List.to_seq [ c; left; right ]
            | _ -> Seq.cons (Vpl.Cstr.Rat.compl c) (Seq.singleton c))
          (* make combinations of all variants between original and complemented linear condition *)
          |> Seq.product_seq
          (* construct domain from linear inequations *)
          |> Seq.map (fun cstr -> assume (of_cond (Cond.of_cstrs (List.of_seq cstr))) top)
          (* filter out original d *)
          |> Seq.filter (not << equal d))
      ;;

      let of_rational x =
        let num, den = Rational.to_int2 x in
        Q.make (Z.of_int num) (Z.of_int den)
      ;;

      let to_string q =
        if is_bottom q
        then "bottom"
        else (
          let cstrs = get_cstrs q in
          if List.is_empty cstrs
          then "top"
          else List.to_string ~sep:" && " (Vpl.Cstr.Rat.to_string Ident.ofVar) cstrs)
      ;;
    end

    let input_to_interface ({ rationals; integers; bools } : inputs) =
      { integer =
          (fun v ->
            Option.map_or ~default:DZ.top (fun c ->
              DZ.assume
                (DZ.of_cond
                 @@ DZ.Cond.Atom
                      ( DZ.Term.Var (Ident.toVar v)
                      , Vpl.Cstr_type.EQ
                      , DZ.Term.Cte (DZ.Coeff.of_int c) ))
                DZ.top)
            @@ VarMap.find_opt v integers)
      ; rational =
          (fun v ->
            Option.map_or ~default:DQ.top (fun c ->
              DQ.assume
                (DQ.of_cond
                 @@ DQ.Cond.Atom
                      ( DQ.Term.Var (Ident.toVar v)
                      , Vpl.Cstr_type.EQ
                      , DQ.Term.Cte (DQ.of_rational c) ))
                DQ.top)
            @@ VarMap.find_opt v rationals)
      ; bool = (fun v -> VarMap.value ~default:false v bools)
      }
    ;;

    module DQZ = struct
      type t = DQ.t * DZ.t

      let top = DQ.top, DZ.top
      let bottom = DQ.bottom, DZ.bottom
      let is_not_bottom (q, z) = (not (DZ.is_bottom z)) && not (DQ.is_bottom q)

      let not (q, z) =
        let nz = Seq.memoize (DZ.not z)
        and nq = Seq.memoize (DQ.not q) in
        Seq.append_list
          [ Seq.product nq nz
          ; Seq.product nq (Seq.repeat z)
          ; Seq.product (Seq.repeat q) nz
          ]
        |> Seq.filter is_not_bottom
        |> List.of_seq
      ;;

      let meet (q1, z1) (q2, z2) : t = DQ.meet q1 q2, DZ.meet z1 z2
      let to_string (q, z) = Printf.sprintf "Q{%s}Z{%s}" (DQ.to_string q) (DZ.to_string z)
    end

    module type Conj = sig
      type t

      val top : t
      val bottom : t
      val meet : t -> t -> t
      val is_not_bottom : t -> bool
      val to_string : t -> string
      val not : t -> t list
    end

    module Disj (Conj : Conj) = struct
      type t = Conj.t list

      let return e : t = [ e ]
      let return2 e1 e2 : t = [ e1; e2 ]
      let bottom : t = [ Conj.bottom ]
      let top : t = return Conj.top

      let normalize conjs =
        let conjs = List.filter Conj.is_not_bottom conjs in
        match conjs with
        | [] -> [ Conj.bottom ]
        | list -> list
      ;;

      let ( && ) s1 s2 : t =
        Seq.product (List.to_seq s1) (List.to_seq s2)
        |> Seq.map (Tuple.fn2 Conj.meet)
        |> List.of_seq
        |> normalize
      ;;

      let ( || ) s1 s2 : t = List.append s1 s2 |> normalize
      let is_bottom l = not @@ List.exists Conj.is_not_bottom l

      let to_string conjunctions =
        List.to_string ~sep:" || \n" Conj.to_string conjunctions
      ;;

      let not conjunctions : t =
        let r =
          conjunctions
          |> List.map (List.to_seq << Conj.not)
          |> List.to_seq
          |> Seq.product_seq
        in
        r
        |> Seq.map (fun s -> Seq.reduce_left Conj.meet Fun.id s)
        |> List.of_seq
        |> normalize
      ;;

      let bool_equal x y = (x && y) || ((not x) && not y)
    end

    module DQZF = Disj (DQZ)

    module B = struct
      type bool_result = DQZF.t * DQZF.t

      let wrap_const_bool c = if c then DQZF.top, DQZF.bottom else DQZF.bottom, DQZF.top
      let not = Tuple.swap2

      let equal (t1, f1) (t2, f2) =
        DQZF.((t1 && t2) || (f1 && f2), (t1 && f2) || (f1 && t2))
      ;;

      let ( && ) (t1, f1) (t2, f2) : bool_result = DQZF.(t1 && t2, f1 || f2)
      let ( || ) (t1, f1) (t2, f2) : bool_result = DQZF.(t1 || t2, f1 && f2)
      let all = List.reduce_left ( && ) Fun.id
      let any = List.reduce_left ( || ) Fun.id

      type 'e result = (DQZF.t * 'e) list
      type int_result = DZ.a_expr result
      type rat_result = DQ.a_expr result

      let int_do_rel (l : int_result) (r : int_result) rel : bool_result =
        let open Vpl.Cstr_type in
        List.cartesian l r
        |> List.map (fun ((d1, e1), (d2, e2)) ->
          let both = DQZF.(d1 && d2) in
          let assume_in_formula cond =
            List.map (fun (q, z) -> q, DZ.assume cond z) both
          in
          let convex_comparisons relt relf =
            let tcond = DZ.of_cond @@ DZ.Cond.Atom (e1, relt, e2)
            and fcond = DZ.of_cond @@ DZ.Cond.Atom (e1, relf, e2) in
            assume_in_formula tcond, assume_in_formula fcond
          in
          let equal_comparisons swap_branches =
            let t = DZ.of_cond @@ DZ.Cond.Atom (e1, EQ, e2)
            and f1 = DZ.of_cond @@ DZ.Cond.Atom (e1, LT, e2)
            and f2 = DZ.of_cond @@ DZ.Cond.Atom (e1, GT, e2) in
            let t = assume_in_formula t
            and f = List.append (assume_in_formula f1) (assume_in_formula f2) in
            if swap_branches then f, t else t, f
          in
          match rel with
          | `Less -> convex_comparisons LT GE
          | `LessEq -> convex_comparisons LE GT
          | `More -> convex_comparisons GT LE
          | `MoreEq -> convex_comparisons GE LT
          | `Eq -> equal_comparisons false
          | `Neq -> equal_comparisons true)
        |> List.reduce_left ( || ) Fun.id
      ;;

      let rat_do_rel (l : rat_result) (r : rat_result) rel : bool_result =
        let open Vpl.Cstr_type in
        List.cartesian l r
        |> List.map (fun ((d1, e1), (d2, e2)) ->
          let both = DQZF.(d1 && d2) in
          let assume_in_formula cond =
            List.map (fun (q, z) -> DQ.assume cond q, z) both
          in
          let convex_comparisons relt relf =
            let tcond = DQ.of_cond @@ DQ.Cond.Atom (e1, relt, e2)
            and fcond = DQ.of_cond @@ DQ.Cond.Atom (e1, relf, e2) in
            assume_in_formula tcond, assume_in_formula fcond
          in
          let equal_comparisons swap_branches =
            let t = DQ.of_cond @@ DQ.Cond.Atom (e1, EQ, e2)
            and f1 = DQ.of_cond @@ DQ.Cond.Atom (e1, LT, e2)
            and f2 = DQ.of_cond @@ DQ.Cond.Atom (e1, GT, e2) in
            let t = assume_in_formula t
            and f = List.append (assume_in_formula f1) (assume_in_formula f2) in
            if swap_branches then f, t else t, f
          in
          match rel with
          | `Less -> convex_comparisons LT GE
          | `LessEq -> convex_comparisons LE GT
          | `More -> convex_comparisons GT LE
          | `MoreEq -> convex_comparisons GE LT
          | `Eq -> equal_comparisons false
          | `Neq -> equal_comparisons false)
        |> List.reduce_left ( || ) Fun.id
      ;;

      let wrap_result e = [ DQZF.top, e ]
    end
    (* module B = struct
      type bool_result = DQZF.t

      let wrap_const_bool c = if c then DQZF.top else DQZF.bottom

      include DQZF

      let equal = DQZF.bool_equal
      let all = List.reduce_left ( && ) Fun.id
      let any = List.reduce_left ( || ) Fun.id

      type 'e result = (DQZF.t * 'e) list
      type int_result = DZ.a_expr result
      type rat_result = DQ.a_expr result

      let int_do_rel (l : int_result) (r : int_result) rel : bool_result =
        let open Vpl.Cstr_type in
        List.cartesian l r
        |> List.map (fun ((d1, e1), (d2, e2)) ->
          let both = DQZF.(d1 && d2) in
          let assume_in_formula cond =
            List.map (fun (q, z) -> q, DZ.assume cond z) both
          in
          let convex_comparisons relt =
            let tcond = DZ.of_cond @@ DZ.Cond.Atom (e1, relt, e2) in
            assume_in_formula tcond
          in
          let equal_comparisons swap_branches =
            let t = DZ.of_cond @@ DZ.Cond.Atom (e1, EQ, e2)
            and f1 = DZ.of_cond @@ DZ.Cond.Atom (e1, LT, e2)
            and f2 = DZ.of_cond @@ DZ.Cond.Atom (e1, GT, e2) in
            let t = assume_in_formula t
            and f = List.append (assume_in_formula f1) (assume_in_formula f2) in
            if swap_branches then f else t
          in
          match rel with
          | `Less -> convex_comparisons LT
          | `LessEq -> convex_comparisons LE
          | `More -> convex_comparisons GT
          | `MoreEq -> convex_comparisons GE
          | `Eq -> equal_comparisons false
          | `Neq -> equal_comparisons true)
        |> List.reduce_left ( || ) Fun.id
      ;;

      let rat_do_rel (l : rat_result) (r : rat_result) rel : bool_result =
        let open Vpl.Cstr_type in
        List.cartesian l r
        |> List.map (fun ((d1, e1), (d2, e2)) ->
          let both = DQZF.(d1 && d2) in
          let assume_in_formula cond =
            List.map (fun (q, z) -> DQ.assume cond q, z) both
          in
          let convex_comparisons relt =
            let tcond = DQ.of_cond @@ DQ.Cond.Atom (e1, relt, e2) in
            assume_in_formula tcond
          in
          let equal_comparisons swap_branches =
            let t = DQ.of_cond @@ DQ.Cond.Atom (e1, EQ, e2)
            and f1 = DQ.of_cond @@ DQ.Cond.Atom (e1, LT, e2)
            and f2 = DQ.of_cond @@ DQ.Cond.Atom (e1, GT, e2) in
            let t = assume_in_formula t
            and f = List.append (assume_in_formula f1) (assume_in_formula f2) in
            if swap_branches then f else t
          in
          match rel with
          | `Less -> convex_comparisons LT
          | `LessEq -> convex_comparisons LE
          | `More -> convex_comparisons GT
          | `MoreEq -> convex_comparisons GE
          | `Eq -> equal_comparisons false
          | `Neq -> equal_comparisons true)
        |> List.reduce_left ( || ) Fun.id
      ;;

      let wrap_result e = [ DQZF.top, e ]
    end *)

    let get_iqueue state var = state.int_queue var
    let get_rqueue state var = state.rat_queue var

    let trace expr (t, f) =
      Format.printf
        "EXPRESSION:%a\n"
        Sexplib0.Sexp.pp_hum
        (sexp_of_bool_expr sexp_of_string sexp_of_string expr);
      Format.printf "-------------------------------------------\n";
      Format.printf "-> TRUE:\n%s\n" (DQZF.to_string t);
      Format.printf "-> FALSE:\n%s\n\n" (DQZF.to_string f)
    ;;

    (** Evaluate Boolean formula given state and input values. *)
    let rec eval_bool
              (state : 'sv state_interface)
              (inputs : ('iv, DZ.t, DQ.t) input_interface)
              (expr : ('sv, 'iv) bool_expr)
      : B.bool_result
      =
      let result =
        match expr with
        | BConst c -> B.wrap_const_bool c
        | BStateVar v -> B.wrap_const_bool (state.bool v)
        | BInputVar v -> B.wrap_const_bool (inputs.bool v)
        | BNot e -> B.not (eval_bool state inputs e)
        | BAnd conjunctions -> List.map (eval_bool state inputs) conjunctions |> B.all
        | BOr disjunctions -> List.map (eval_bool state inputs) disjunctions |> B.any
        | BEq (e1, e2) -> B.equal (eval_bool state inputs e1) (eval_bool state inputs e2)
        | BNeq (e1, e2) ->
          B.not (B.equal (eval_bool state inputs e1) (eval_bool state inputs e2))
        | BImply (e1, e2) ->
          B.((not (eval_bool state inputs e1)) || eval_bool state inputs e2)
        | IntComp (e1, rel, e2) ->
          let l = eval_integer state inputs e1
          and r = eval_integer state inputs e2 in
          
          Format.printf "LEFT: %s\n" @@ List.to_string Fun.id  (List.map (fun (d, e) -> Printf.sprintf "%s -> %s" (DQZF.to_string d) (DZ.a_expr_to_string e) ) l);
          Format.printf "RIGHT: %s\n" @@ List.to_string Fun.id  (List.map (fun (d, e) -> Printf.sprintf "%s -> %s" (DQZF.to_string d) (DZ.a_expr_to_string e) ) r);
          B.int_do_rel l r rel
        | RatComp (e1, rel, e2) ->
          B.rat_do_rel (eval_rational state inputs e1) (eval_rational state inputs e2) rel
        | BITE { cond; if_true; if_false } ->
          let t, f = eval_bool state inputs cond in
          let tt, tf =
            if DQZF.is_bottom t
            then DQZF.bottom, DQZF.top
            else eval_bool state inputs if_true
          and ft, ff =
            if DQZF.is_bottom f
            then DQZF.top, DQZF.bottom
            else eval_bool state inputs if_false
          in
          DQZF.((t && tt) || (f && ft), (t && tf) || (f && ff))
        | IntQueuePositive q ->
          B.wrap_const_bool @@ Queue.for_all (Integer.less_eq 0) (get_iqueue state q)
      in
      (* trace expr result; *)
      result

    (** Evaluate integer expression given state and input values. *)
    and eval_integer state inputs : _ -> B.int_result = function
      | IConst c -> B.wrap_result @@ DZ.Term.Cte (DZ.Coeff.of_int c)
      | IStateVar var ->
        B.wrap_result @@ DZ.Term.Cte (DZ.Coeff.of_int @@ state.integer var)
      | IInputVar var -> [ [ DQ.top, inputs.integer var ], DZ.Term.Var (Ident.toVar var) ]
      | IBinOp (e1, op, e2) ->
        let r1 = eval_integer state inputs e1
        and r2 = eval_integer state inputs e2 in
        List.cartesian r1 r2
        |> List.map (fun ((d1, e1), (d2, e2)) ->
          ( DQZF.(d1 && d2)
          , match op with
            | `Div -> DZ.Term.Div (e1, e2)
            | `Add -> DZ.Term.Add (e1, e2)
            | `Sub -> DZ.Term.Add (e1, DZ.Term.Opp e2)
            | `Mul -> DZ.Term.Mul (e1, e2) ))
      | IPeekFirstQueue qe ->
        B.wrap_result @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.peek @@ get_iqueue state qe)
      | IPeekLastQueue qe ->
        B.wrap_result @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.last @@ get_iqueue state qe)
      | IntQueueLength qe ->
        B.wrap_result
        @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.length @@ get_iqueue state qe)
      | RatQueueLength qe ->
        B.wrap_result
        @@ DZ.Term.Cte (DZ.Coeff.of_int @@ Queue.length @@ get_rqueue state qe)
      | IITE { cond; if_true; if_false } ->
        let t, f = eval_bool state inputs cond
        and rt = eval_integer state inputs if_true
        and rf = eval_integer state inputs if_false in
        List.append
          (List.map (fun (d, e) -> DQZF.(t && d), e) rt)
          (List.map (fun (d, e) -> DQZF.(f && d), e) rf)

    (** Evaluate rational expression given state and input values. *)
    and eval_rational state inputs : _ -> B.rat_result = function
      | RConst c -> B.wrap_result @@ DQ.Term.Cte (DQ.of_rational c)
      | RStateVar var ->
        B.wrap_result @@ DQ.Term.Cte (DQ.of_rational @@ state.rational var)
      | RInputVar var ->
        [ [ inputs.rational var, DZ.top ], DQ.Term.Var (Ident.toVar var) ]
      | RBinOp (e1, op, e2) ->
        let r1 = eval_rational state inputs e1
        and r2 = eval_rational state inputs e2 in
        List.cartesian r1 r2
        |> List.map (fun ((d1, e1), (d2, e2)) ->
          ( DQZF.(d1 && d2)
          , match op with
            | `Div -> DQ.Term.Div (e1, e2)
            | `Add -> DQ.Term.Add (e1, e2)
            | `Sub -> DQ.Term.Add (e1, DQ.Term.Opp e2)
            | `Mul -> DQ.Term.Mul (e1, e2) ))
      | RPeekFirstQueue qe ->
        B.wrap_result @@ DQ.Term.Cte (DQ.of_rational @@ Queue.peek @@ get_rqueue state qe)
      | RPeekLastQueue qe ->
        B.wrap_result @@ DQ.Term.Cte (DQ.of_rational @@ Queue.last @@ get_rqueue state qe)
      | RITE { cond; if_true; if_false } ->
        let t, f = eval_bool state inputs cond
        and rt = eval_rational state inputs if_true
        and rf = eval_rational state inputs if_false in
        List.append
          (List.map (fun (d, e) -> DQZF.(t && d), e) rt)
          (List.map (fun (d, e) -> DQZF.(f && d), e) rf)
    ;;
  end

  type transition_error =
    | NoValidTransition
    | FailedGuard
    | FailedInvariant

  let transition_error_to_string = function
    | NoValidTransition -> "no valid transition"
    | FailedGuard -> "failed guard"
    | FailedInvariant -> "failed invariant"
  ;;

  let do_transition
        ~input_to_interface
        ~eval_guard
        { transitions; invariant }
        state
        inputs
    =
    Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string (sexp_of_state state);
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

  let apply_transition =
    do_transition ~input_to_interface:Full.input_to_interface ~eval_guard:Full.eval_bool
  ;;

  let accept_transition =
    do_transition ~input_to_interface:Partial.input_to_interface ~eval_guard:(fun s i c ->
      let t, _ = Partial.eval_bool s i c in
      Format.printf "END OF GUARD EVALUATION:\n%s\n" (Partial.DQZF.to_string t);
      not @@ Partial.DQZF.is_bottom t)
  ;;
end

module Syntax = struct
  (** Syntax for the machine creation. *)

  (** Integers *)

  let ( > ) x y = IntComp (x, `More, y)
  let ( < ) x y = IntComp (x, `Less, y)
  let ( >= ) x y = IntComp (x, `MoreEq, y)
  let ( <= ) x y = IntComp (x, `LessEq, y)
  let ( == ) x y = IntComp (x, `Eq, y)
  let ( != ) x y = IntComp (x, `Neq, y)
  let iconst x = IConst x
  let ( + ) x y = IBinOp (x, `Add, y)
  let ( - ) x y = IBinOp (x, `Sub, y)
  let ( * ) x y = IBinOp (x, `Mul, y)
  let ( / ) x y = IBinOp (x, `Div, y)
  let iite cond if_true if_false = IITE { cond; if_true; if_false }
  let iinvar v = IInputVar v

  let iitec cond if_true if_false =
    IITE { cond; if_true = iconst if_true; if_false = iconst if_false }
  ;;

  let ilength q = IntQueueLength q
  let rlength q = RatQueueLength q
  let i0 = iconst 0
  let i1 = iconst 1

  (** Rationals *)

  let rinvar v = RInputVar v
  let rsvar v = RStateVar v
  let ( >. ) x y = RatComp (x, `More, y)
  let ( <. ) x y = RatComp (x, `Less, y)
  let ( >=. ) x y = RatComp (x, `MoreEq, y)
  let ( <=. ) x y = RatComp (x, `LessEq, y)
  let ( ==. ) x y = RatComp (x, `Eq, y)
  let ( !=. ) x y = RatComp (x, `Neq, y)
  let rconst x = RConst x
  let ( +. ) x y = RBinOp (x, `Add, y)
  let ( -. ) x y = RBinOp (x, `Sub, y)
  let ( *. ) x y = RBinOp (x, `Mul, y)
  let ( /. ) x y = RBinOp (x, `Div, y)
  let rite cond if_true if_false = RITE { cond; if_true; if_false }
  let r0 = RConst Rational.zero

  (** Booleans *)

  (** True constant. *)
  let t = BConst true

  (** False constant. *)
  let f = BConst false

  (** Boolean input variable. *)
  let binvar v = BInputVar v

  (** Boolean state variable. *)
  let bsvar v = BStateVar v

  (** Boolean conjunction. *)
  let ( && ) x y = BAnd [ x; y ]

  (** Boolean disjunction. *)
  let ( || ) x y = BOr [ x; y ]

  (** Boolean implication. [x ==> y = !x || y]*)
  let ( ==> ) x y = BImply (x, y)

  (** Boolean equality (iff). *)
  let ( <=> ) x y = BEq (x, y)

  (** Boolean inequality. [a <!> b = !(a <=> y)]*)
  let ( <!> ) x y = BNeq (x, y)

  (** Boolean negation. *)
  let ( ! ) x = BNot x

  (** Boolean if-then-else. *)
  let bite cond if_true if_false = BITE { cond; if_true; if_false }

  (** Integer queues *)

  let iqueue symbol = IQVar symbol
  let ipush q e = IPushQueue (q, e)
  let ipop q = IPopQueue q
  let ifirst q = IPeekFirstQueue q
  let ilast q = IPeekLastQueue q
  let all_positive q = IntQueuePositive q
  let decrease q = IDecreaseAllQueue q
  let increase q = IIncreaseAllQueue q
  let iqite cond if_true if_false = IQITE { cond; if_true; if_false }

  (** rational queues *)

  let rqueue symbol = RQVar symbol
  let rpush q e = RPushQueue (q, e)
  let rpop q = RPopQueue q
  let rfirst q = RPeekFirstQueue q
  let rlast q = RPeekLastQueue q
  let rqite cond if_true if_false = RQITE { cond; if_true; if_false }

  (** Machine description. *)

  (** State and input guard maps into variable assignments. *)
  let ( |-> ) (state_cond, input_cond) assignments =
    { state_cond; input_cond; assignments }
  ;;

  (** State guard and input guard. *)
  let ( @@@ ) state_cond input_cond = state_cond, input_cond

  (** Transition description with invariant. *)
  let ( &&& ) transitions invariant = { transitions; invariant }

  let ( = ) v' e = v', IntExpr e
  let ( =. ) v' e = v', RatExpr e
  let ( =& ) v' e = v', BoolExpr e
  let ( =| ) v' e = v', IntQueueExpr e
  let ( =|. ) v' e = v', RatQueueExpr e
end
