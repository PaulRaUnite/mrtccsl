(** Calculus of communicating systems. *)

type 'v vector = 'v list
type effect_call = unit -> unit

(** Action type. *)
type ('e, 'var, 'value) action =
  | Send of 'e * 'value (** Send action. *)
  | Receive of 'e * 'var (** Receive action. *)
  | Tau (** Tau represents unobservable action. *)

(** Inverts send and receive. Tau cannot be changed. *)
let invert_action = function
  | Send (e, v) -> Receive (e, v)
  | Receive (e, v) -> Send (e, v)
  | Tau -> Tau
;;

(** Function that returns *)
type ('e, 'var, 'value) closure_process = 'value vector -> ('e, 'var, 'value) process

and ('e, 'var, 'value) process =
  | Nil (** End of process. *)
  | Prefix of ('e, 'var, 'value) action * ('e, 'var, 'value) process
  (** Action followed by process. *)
  | Parallel of ('e, 'var, 'value) process * ('e, 'var, 'value) process
  (** Parallel pair of processes. *)
  | Choice of ('e, 'var, 'value) process * ('e, 'var, 'value) process
  (** Choice between the processes. *)
  | Restrict of 'e * ('e, 'var, 'value) process
  (** Introduction of action. Essentially hides an action. *)
  | Substitute of ('e, 'var, 'var) process * ('var * 'value) vector
  (** Replaces variables in value places in a process with value parameters. *)
  | Closure of ('e, 'var, 'value) closure_process * 'value vector
  (** Process that is unwrapped with function call. May perform effectful actions in the host language on captured values. *)

module Syntax = struct
  let nil = Nil
  let[@inline always] ( @! ) (e, v) p = Prefix (Send (e, v), p)
  let[@inline always] ( @? ) (e, v) p = Prefix (Receive (e, v), p)
  let[@inline always] ( + ) p1 p2 = Choice (p1, p2)
  let[@inline always] ( || ) p1 p2 = Parallel (p1, p2)
  let[@inline always] ( .@[] ) p substitution = Substitute (p, substitution)

  let map ~f ~vars p values =
    let closure =
      fun vector ->
      let substitution = List.map2 f vars vector in
      Substitute (p, substitution)
    in
    Closure (closure, values)
  ;;
end

module ProcessDefinitions = struct
  (** 
  Queue process, recursively defined as:
   {math \begin{aligned}
    Q_2(in, out) &= in(y).Q1(in, out)〈y〉\\
    Q_1(in, out)\langle y \rangle &= in(z).Q_0(in, out)\langle z, y \rangle + \overline{out}\langle y \rangle.Q_2(in, out)\\
    Q_0(in, out)\langle z, y \rangle &= \overline{out}\langle y \rangle.Q_1(in, out)\langle z \rangle
\end{aligned} } *)
  let queue ~anon input output =
    let y = anon 0 in
    let z = anon 1 in
    let rec q2 = Prefix (Receive (input, y), Substitute (q1, [ y, y ]))
    and q1 = Choice (q11, q12)
    and q11 = Prefix (Receive (input, z), Substitute (q0, [ z, z; y, y ]))
    and q12 = Prefix (Send (output, y), q2)
    and q0 = Prefix (Send (output, y), Substitute (q1, [ y, z ])) in
    q2
  ;;

  (**
  Variable defined as:
  {math V(w,r)\langle v \rangle = w(x). V(w,r)\langle x \rangle + \overline{r}\langle v \rangle . V(w,r)\langle v \rangle }
  *)
  let variable ~anon write read initial =
    let v = anon 0 in
    let x = anon 1 in
    let rec pw = Prefix (Receive (write, x), Substitute (p, [ v, x ]))
    and pr = Prefix (Send (read, v), Substitute (p, [ v, v ]))
    and p = Choice (pw, pr) in
    Substitute (p, [ v, initial ])
  ;;
end

open Common

module type Event = sig
  include Interface.TotalOrder
end

module type Variable = sig
  include Interface.TotalOrder
end

module DefaultVariable (V : Interface.TotalOrder) = struct
  open Ppx_compare_lib.Builtin

  type t =
    | Explicit of V.t
    | Anon of int
  [@@deriving compare]

  let to_string v = Printf.sprintf "anon.%i" v
  let explicit v = Explicit v
  let anon index = Anon index
end


module Execution (E : Event) (V : Variable) = struct end
