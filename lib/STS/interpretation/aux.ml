open Common 
open Prelude
open Number

type var = string

(** Map from variables to (typically) their values. *)
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

let empty_input_interface : (Def.empty, _, _) input_interface =
  let impossible _ = failwith "impossible situation, empty type has inhabitants" in
  { integer = impossible; rational = impossible; bool = impossible }
;;
