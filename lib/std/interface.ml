module type Stringable = sig
  type t

  val to_string : t -> string
end

module type Parseble = sig
  type t

  val of_string : string -> t
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

    (**[less x y] is [x < y]*)
    let[@inline always] less x y = M.compare x y < 0

    (**[more x y] is [x > y]*)
    let[@inline always] more x y = M.compare x y > 0

    (**[equal x y] is [x == y]*)
    let[@inline always] equal x y = M.compare x y = 0

    (**[less_eq x y] is [x <= y]*)
    let[@inline always] less_eq x y = M.compare x y <= 0

    (**[more_eq x y] is [x >= y]*)
    let[@inline always] more_eq x y = M.compare x y >= 0

    let[@inline always] min x y = if less_eq x y then x else y
    let[@inline always] max x y = if more_eq x y then x else y

    module Operators = struct
      let ( = ) = equal
      let ( <> ) x y = not (equal x y)
      let ( < ) = less
      let ( <= ) = less_eq
      let ( > ) = more
      let ( >= ) = more_eq
    end
  end
end

module Number = struct
  module type Ring = sig
    type t

    val zero : t
    val one : t
    val add : t -> t -> t
    val mul : t -> t -> t
  end

  module type Field = sig
    include Ring

    val neg : t -> t
    val sub : t -> t -> t
    val div : t -> t -> t
  end

  module Operators = struct
    module type S = sig
      type t

      val ( + ) : t -> t -> t
      val ( - ) : t -> t -> t
      val ( * ) : t -> t -> t
      val ( / ) : t -> t -> t
      val ( ~- ) : t -> t
    end

    module Make (F : Field) = struct
      include F

      let ( ~- ) = neg
      let ( + ) = add
      let ( - ) = sub
      let ( * ) = mul
      let ( / ) = div
    end
  end
end

module type Foldable = sig
  type 'a t

  val fold_left : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
end
