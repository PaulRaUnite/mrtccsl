open Common

module type ID = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
  include Interface.Stringable with type t := t
end

module type ExtIDs = sig
  (** Place IDs. *)
  module Place : ID

  (** Transition IDs. *)
  module Transition : ID

  (** Color IDs. *)
  module Color : ID

  (** Event IDs. *)
  module Event : ID

  (** Probe IDs. *)
  module Probe : ID
end

module type IDs = sig
  (** Place IDs. *)
  module Place : ID

  (** Color IDs. *)
  module Color : ID

  (** Event IDs. *)
  module Event : ID

  (** Probe IDs. *)
  module Probe : ID
end

(** Timestamps. *)
module type Time = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
  include Interface.Number.Ring with type t := t
  include Interface.Stringable with type t := t
end
