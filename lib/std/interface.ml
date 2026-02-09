(** Signature of convertible to a string type. *)
module type Stringable = sig
  type t

  val to_string : t -> string
end

(** Signature of convertible from a string type. *)
module type Parseable = sig
  type t

  val of_string : string -> t
end

(** Signature of debuggable type (sexp and string convertible). *)
module type Debug = sig
  include Sexplib0.Sexpable.S
  include Stringable with type t := t
end

(** Signature of a totally ordered type. *)
module type TotalOrder = Set.OrderedType

(** Extended order functions.*)
module ExpOrder = struct
  module type S = sig
    type t

    (** Total comparison of two elements. *)
    val compare : t -> t -> int

    (** Computes [x < y]. *)
    val less : t -> t -> bool

    (** Computes [x > y]. *)
    val more : t -> t -> bool

    (** Computes [x = y]. *)
    val equal : t -> t -> bool

    (** Computes [x <= y]. *)
    val less_eq : t -> t -> bool

    (** Computes [x .= y]. *)
    val more_eq : t -> t -> bool

    (** Computes the smallest element out of two. *)
    val min : t -> t -> t

    (** Computes the biggest element out of two. *)
    val max : t -> t -> t
  end

  module Make (M : TotalOrder) = struct
    include M

    let compare = M.compare

    (** Computes [x < y]*)
    let[@inline always] less x y = M.compare x y < 0

    (** Computes [x > y]*)
    let[@inline always] more x y = M.compare x y > 0

    (** Computes [x == y]*)
    let[@inline always] equal x y = M.compare x y = 0

    (** Computes is [x <= y]*)
    let[@inline always] less_eq x y = M.compare x y <= 0

    (** Computes is [x >= y]*)
    let[@inline always] more_eq x y = M.compare x y >= 0

    (** Computes the smallest element out of two. *)
    let[@inline always] min x y = if less_eq x y then x else y

    (** Computes the biggest element out of two. *)
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
    (** Signature of a ring. *)

    (** Ring is assumed to satisfty the following axioms:
    {ul 
        {- For addition:
          + associativity {m (a + b) + c = a + (b + c)}
          + commutativity {m a + b = b + a}
          + 0-identity {m a + 0 = 0 + a = a}
          + existence of inverse {m a + (-a) = 0 }}
        {- For multiplication:
          + associativity {m (a \cdot b) \cdot c = a \cdot (b \cdot c) }
          + 1-identity {m 1\cdot a = a\cdot 1 = a}}
        {- For the two:
          + left distributivity {m a\cdot (b + c) = (a\cdot b) + (a \cdot b)}
          + right distributivity {m (b+c) \cdot a = (b\cdot a) + (c \cdot a)}}
          }
*)

    (** Ring element type. *)
    type t

    (** 0 element. *)
    val zero : t

    (** 1 element. *)
    val one : t

    (** Negation operator. *)
    val neg : t -> t

    (** Addition operation. *)
    val add : t -> t -> t

    (** Multiplication operation. *)
    val mul : t -> t -> t

    (** Subtraction operation. *)
    val sub : t -> t -> t
  end

  module type Field = sig
    (** Signature of a field. *)

    (** Field includes all definitions and exioms of {!Ring}, plus multiplicative inverse {m \forall a \neq 0: a\cdot a^{-1} = 1}. *)

    include Ring

    (** Division operation, [x / y], [y \neq 0]. *)
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

(** Signature of a type that can be traversed by folding. *)
module type Foldable = sig
  (** Container type. *)
  type 'a t

  (** Traverses the container elements. *)
  val fold : ('acc -> 'a -> 'acc) -> 'acc -> 'a t -> 'acc
end
