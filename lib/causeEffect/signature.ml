open Common

module type ID = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
  include Interface.Stringable with type t := t
end

module type IDs = sig
  (** Place IDs. *)
  module Place : ID

  (** Chain IDs. *)
  module Color : ID

  (** Probe IDs. *)
  module Probe : ID

  (** Event IDs. *)
  module Event : ID
end

module type ExtIDs = sig
  include IDs

  (** Transition IDs. *)
  module Transition : ID
end

(** Timestamps. *)
module type Time = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
  include Interface.Number.Field with type t := t
  include Interface.Stringable with type t := t
end
