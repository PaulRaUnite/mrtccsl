open! Prelude

module type Stringable = sig
  type t

  val to_string : t -> string
end

module type Debug = sig
  include Sexplib0.Sexpable.S
  include Stringable with type t := t
end

module type OrderedType = Set.OrderedType

module ExpOrder = struct
  module type S = sig
    type t

    val compare : t -> t -> int
    val less : t -> t -> bool
    val more : t -> t -> bool
    val equal : t -> t -> bool
    val less_eq : t -> t -> bool
    val more_eq : t -> t -> bool
    val min : t -> t -> t
    val max : t -> t -> t
  end

  module Make (M : OrderedType) = struct
    include M

    let compare = M.compare
    let less x y = M.compare x y < 0
    let more x y = M.compare x y > 0
    let equal x y = M.compare x y = 0
    let less_eq x y = M.compare x y <= 0
    let more_eq x y = M.compare x y >= 0
    let min x y = if less_eq x y then x else y
    let max x y = if more_eq x y then x else y
  end
end

module Number = struct
  module type Ring = sig
    type t

    val zero : t
    val one : t
    val ( + ) : t -> t -> t
    val ( * ) : t -> t -> t
  end

  module type Field = sig
    include Ring

    val neg : t -> t
    val ( - ) : t -> t -> t
    val ( / ) : t -> t -> t
  end
end
