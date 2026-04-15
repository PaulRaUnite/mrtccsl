open Common
open Number
open Aux
open Def

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
    Expr.do_rel
      ~compare:Int.compare
      rel
      (eval_integer state inputs e1)
      (eval_integer state inputs e2)
  | RatComp (e1, rel, e2) ->
    Expr.do_rel
      ~compare:Rational.compare
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
