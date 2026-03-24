open Common

module type S = functor (IDs : Signature.IDs) (Time : Signature.Time) -> sig
  type t

  open IDs

  module Token :
    Token.S with type event = Event.t and type time = Time.t and type color = Color.t

  val of_decl : (Event.t, Place.t, Color.t, Probe.t) Declaration.t -> t

  val consume_trace
    :  t
    -> start:(Probe.t -> Time.t -> unit)
    -> finish:(Probe.t -> Token.t -> unit)
    -> (Event.t, Time.t) Trace.t
    -> unit
end