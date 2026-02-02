open Prelude
open Number
open Expr
module VarMap = Map.Make (String)

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
end

type ('b, 'v) ite =
  { cond : 'b
  ; if_true : 'v
  ; if_false : 'v
  }

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
  | IntQueuePositive of ('sv, 'iv) int_queue_expr

and ('sv, 'iv) int_expr =
  | IConst of int
  | IStateVar of 'sv
  | IInputVar of 'iv
  | IBinOp of ('sv, 'iv) int_expr * num_op * ('sv, 'iv) int_expr
  | IITE of (('sv, 'iv) bool_expr, ('sv, 'iv) int_expr) ite
  | IPeekFirstQueue of ('sv, 'iv) int_queue_expr
  | IPeekLastQueue of ('sv, 'iv) int_queue_expr
  | IntQueueLength of ('sv, 'iv) int_queue_expr
  | RatQueueLength of ('sv, 'iv) rat_queue_expr

and ('sv, 'iv) rat_expr =
  | RConst of Rational.t
  | RStateVar of 'sv
  | RInputVar of 'iv
  | RITE of (('sv, 'iv) bool_expr, ('sv, 'iv) rat_expr) ite
  | RBinOp of ('sv, 'iv) rat_expr * num_op * ('sv, 'iv) rat_expr
  | RPeekFirstQueue of ('sv, 'iv) rat_queue_expr
  | RPeekLastQueue of ('sv, 'iv) rat_queue_expr

and ('sv, 'iv) int_queue_expr =
  | IQVar of 'sv
  | IPushQueue of ('sv, 'iv) int_queue_expr * ('sv, 'iv) int_expr
  | IPopQueue of ('sv, 'iv) int_queue_expr
  | IDecreaseAllQueue of ('sv, 'iv) int_queue_expr
  | IQITE of (('sv, 'iv) bool_expr, ('sv, 'iv) int_queue_expr) ite

and ('sv, 'iv) rat_queue_expr =
  | RQVar of 'sv
  | RPushQueue of ('sv, 'iv) rat_queue_expr * ('sv, 'iv) rat_expr
  | RPopQueue of ('sv, 'iv) rat_queue_expr
  | RQITE of (('sv, 'iv) bool_expr, ('sv, 'iv) rat_queue_expr) ite

type ('sv, 'iv) expr =
  | BoolExpr of ('sv, 'iv) bool_expr
  | IntExpr of ('sv, 'iv) int_expr
  | RatExpr of ('sv, 'iv) rat_expr
  | IntQueueExpr of ('sv, 'iv) int_queue_expr
  | RatQueueExpr of ('sv, 'iv) rat_queue_expr

type ('sv, 'iv) guard = ('sv, 'iv) bool_expr
type ('sv, 'iv) assignment = 'sv * ('sv, 'iv) expr

type ('sv, 'iv) transition =
  { state_cond : ('sv, empty) bool_expr
    (** Condition on state variables that identifies the partition. *)
  ; input_cond : ('sv, 'iv) bool_expr
    (** Input condition of the form [S -> 2^(B^n * Q)], where [B^n] encodes the clock ticks and [Q] encodes next possible time. *)
  ; assignments : ('sv, 'iv) assignment list
    (** List of actions performed on the state variables using previous state and inputs [S * B^n * Q -> S]*)
  }

type ('sv, 'iv) t =
  { transitions : ('sv, 'iv) transition list
  ; invariant : ('sv, 'iv) bool_expr
  }

type inputs =
  { rationals : Rational.t VarMap.t
  ; integers : int VarMap.t
  ; bools : bool VarMap.t
  }

type state =
  { integers : int VarMap.t (* 0 *)
  ; rationals : Rational.t VarMap.t (* -1 *)
  ; bools : bool VarMap.t (* false *)
  ; int_queues : int Queue.t VarMap.t (* [] *)
  ; rat_queues : Rational.t Queue.t VarMap.t (* [] *)
  }

let rec eval_bool state inputs =
  let evalb = eval_bool state inputs in
  function
  | BConst c -> c
  | BStateVar v -> VarMap.value ~default:false v state.bools
  | BInputVar v -> VarMap.value ~default:false v inputs.bools
  | BNot e -> not (evalb e)
  | BAnd conjunctions -> List.for_all evalb conjunctions
  | BOr disjunctions -> List.exists evalb disjunctions
  | BEq (e1, e2) -> Bool.equal (evalb e1) (evalb e2)
  | BNeq (e1, e2) -> not (Bool.equal (eval_bool state inputs e1) (evalb e2))
  | BImply (e1, e2) -> (not (evalb e1)) || evalb e2
  | IntComp (e1, rel, e2) ->
    do_rel Int.compare rel (eval_integer state inputs e1) (eval_integer state inputs e2)
  | RatComp (e1, rel, e2) ->
    do_rel
      Rational.compare
      rel
      (eval_rational state inputs e1)
      (eval_rational state inputs e2)
  | BITE { cond; if_true; if_false } ->
    if evalb cond then evalb if_true else evalb if_false
  | IntQueuePositive q ->
    Queue.for_all (Integer.less_eq 0) (eval_int_queue state inputs q)

and eval_integer state inputs = function
  | IConst c -> c
  | IStateVar var -> VarMap.value ~default:0 var state.integers
  | IInputVar var -> VarMap.value ~default:0 var inputs.integers
  | IBinOp (e1, op, e2) ->
    let e1 = eval_integer state inputs e1
    and e2 = eval_integer state inputs e2 in
    (match op with
     | `Div -> Int.div e1 e2
     | `Add -> Int.add e1 e2
     | `Sub -> Int.sub e1 e2
     | `Mul -> Int.mul e1 e2)
  | IPeekFirstQueue qe ->
    let qe = eval_int_queue state inputs qe in
    Queue.peek qe
  | IPeekLastQueue qe ->
    let qe = eval_int_queue state inputs qe in
    Queue.last qe
  | IntQueueLength qe ->
    let qe = eval_int_queue state inputs qe in
    Queue.length qe
  | RatQueueLength qe ->
    let qe = eval_rat_queue state inputs qe in
    Queue.length qe
  | IITE { cond; if_true; if_false } ->
    if eval_bool state inputs cond
    then eval_integer state inputs if_true
    else eval_integer state inputs if_false

and eval_rational state inputs = function
  | RConst c -> c
  | RStateVar var -> VarMap.value ~default:Rational.zero var state.rationals
  | RInputVar var -> VarMap.value ~default:Rational.zero var inputs.rationals
  | RBinOp (e1, op, e2) ->
    let e1 = eval_rational state inputs e1
    and e2 = eval_rational state inputs e2 in
    (match op with
     | `Div -> Rational.div e1 e2
     | `Add -> Rational.add e1 e2
     | `Sub -> Rational.sub e1 e2
     | `Mul -> Rational.mul e1 e2)
  | RPeekFirstQueue qe ->
    let qe = eval_rat_queue state inputs qe in
    Queue.peek qe
  | RPeekLastQueue qe ->
    let qe = eval_rat_queue state inputs qe in
    Queue.last qe
  | RITE { cond; if_true; if_false } ->
    if eval_bool state inputs cond
    then eval_rational state inputs if_true
    else eval_rational state inputs if_false

and eval_int_queue state inputs = function
  | IQVar var -> VarMap.value ~default:Queue.empty var state.int_queues
  | IPushQueue (q, e) ->
    let e = eval_integer state inputs e
    and q = eval_int_queue state inputs q in
    Queue.push e q
  | IPopQueue q ->
    let q = eval_int_queue state inputs q in
    Queue.pop q
  | IDecreaseAllQueue q -> Queue.map Int.pred (eval_int_queue state inputs q)
  | IQITE { cond; if_true; if_false } ->
    eval_int_queue
      state
      inputs
      (if eval_bool state inputs cond then if_true else if_false)

and eval_rat_queue state inputs = function
  | RQVar var -> VarMap.value ~default:Queue.empty var state.rat_queues
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

let transition state inputs assignment =
  let var, expr = assignment in
  let state =
    match expr with
    | BoolExpr e ->
      { state with bools = VarMap.add var (eval_bool state inputs e) state.bools }
    | IntExpr e ->
      { state with
        integers = VarMap.add var (eval_integer state inputs e) state.integers
      }
    | RatExpr e ->
      { state with
        rationals = VarMap.add var (eval_rational state inputs e) state.rationals
      }
    | IntQueueExpr e ->
      { state with
        int_queues = VarMap.add var (eval_int_queue state inputs e) state.int_queues
      }
    | RatQueueExpr e ->
      { state with
        rat_queues = VarMap.add var (eval_rat_queue state inputs e) state.rat_queues
      }
  in
  state
;;

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
