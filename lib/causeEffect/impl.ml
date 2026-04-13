open Common

module type I = sig
  module Event : Signature.ID
  module Chain : Signature.ID
  module Place : Signature.ID
end

module type S = functor (IDs : I) (Time : Signature.Time) -> sig
  type t

  open IDs

  module Token :
    Token.S with type event = Event.t and type time = Time.t and type color = Chain.t

  val of_decl : (Event.t, Place.t, Chain.t) Declaration.t -> t

  val consume_trace
    :  t
    -> start:(Chain.t -> Time.t -> unit)
    -> finish:(Chain.t -> Token.t -> unit)
    -> (Event.t, Time.t) Trace.t
    -> unit
end
