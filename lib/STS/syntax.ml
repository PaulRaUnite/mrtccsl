(** Syntax for the machine creation. *)
open Def

open Common.Number

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
let ( |-> ) (state_cond, input_cond) assignments = { state_cond; input_cond; assignments }

(** State guard and input guard. *)
let ( @@@ ) state_cond input_cond = state_cond, input_cond

(** Transition description with invariant. *)
let ( &&& ) transitions invariant = { transitions; invariant }

(** Assigns integer expression to an integer variable. *)
let ( = ) v' e = v', IntExpr e

(** Assigns rational expression to a rational variable. *)
let ( =. ) v' e = v', RatExpr e

(** Assigns Boolean expression to a Boolean variable. *)
let ( =& ) v' e = v', BoolExpr e

(** Assigns integer queue expression to an integer queue variable. *)
let ( =| ) v' e = v', IntQueueExpr e

(** Assigns rational queue expression to an rational queue variable. *)
let ( =|. ) v' e = v', RatQueueExpr e
