open Sexplib0.Sexp_conv
open Ppx_compare_lib.Builtin

(** Declaration statements. *)
type ('event, 'place, 'chain) statement =
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
      | Chain of {
        name: 'chain;
        alternatives: 'event list list
      } (** Cause-Effect chain declaration. *)
[@@deriving sexp, compare]

type ('event, 'place, 'chain) t = ('event, 'place, 'chain) statement list
[@@deriving sexp, compare]
