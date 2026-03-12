(* module Make (IDs : Signature.ReducedIDs) = struct *)
open Sexplib0.Sexp_conv
open Ppx_compare_lib.Builtin

(** Declaration statements. *)
type ('event, 'place, 'color, 'probe) statement =
  | Variable of
      { name : 'place
      ; writes : 'event list
      ; reads : 'event list
      } (** Shared variable declaration. *)
  | Queue of
      { name : 'place
      ; writes : 'event list
      ; reads : 'event list
      } (** Queue variable declaration. *)
  | Inject of
      { at : 'event
      ; color : 'color
      } (** Color injection declaration. *)
  | Probe of
      { name : 'probe
      ; color : 'color
      ; at : 'event
      } (** Probe declaration. *)
[@@deriving sexp, compare]

type ('event, 'place, 'color, 'probe) t = ('event, 'place, 'color, 'probe) statement list
[@@deriving sexp, compare]

(** Semantics of ends of causal-effect chains. *)
type end_semantics =
  | Early (** Early denotes early cause or effect among equivalent. *)
  | Late (** Late denotes late cause or effect among equivalent. *)
(* end *)
