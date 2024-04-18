open Prelude

module type I = sig
  type num

  type bound =
    | Exclude of num
    | Include of num
    | Inf

  type t =
    | Bound of bound * bound
    | Empty

  val make_include : num -> num -> t
  val make_exclude : num -> num -> t
  val return : num -> t
  val pinf : num -> t
  val ninf : num -> t
  val pinf_strict : num -> t
  val ninf_strict : num -> t
  val empty : t
  val inf : t
  val destr : t -> (bound * bound) option
  val inter : t -> t -> t

  (**x is subset of y**)
  val subset : t -> t -> bool

  val compare : t -> t -> int
  val is_empty : t -> bool

  (**does interval contains a value**)
  val contains : t -> num -> bool

  val shift_by : t -> num -> t
  val ( <-> ) : num -> num -> t
  val ( =-> ) : num -> num -> t
  val ( <-= ) : num -> num -> t
  val ( =-= ) : num -> num -> t

  include Sexplib0.Sexpable.S with type t := t
end

module type Num = sig
  include Set.OrderedType
  include Sexplib0.Sexpable.S with type t := t

  val ( + ) : t -> t -> t
end

module Make (N : Num) = struct
  type num = N.t

  type bound =
    | Exclude of N.t
    | Include of N.t
    | Inf
  [@@deriving sexp]

  open Sexplib0.Sexp_conv

  module Bound = struct
    type t = bound

    let shift_by x n =
      match x with
      | Exclude x -> Exclude N.(x + n)
      | Include x -> Include N.(x + n)
      | Inf -> Inf
    ;;

    let neg = function
      | Exclude x -> Some (Include x)
      | Include x -> Some (Exclude x)
      | Inf -> None
    ;;
  end

  module LeftBound = ExpOrder.Make (struct
      type t = Bound.t

      let compare x y =
        match x, y with
        | Exclude x, Exclude y | Include x, Include y -> N.compare x y
        | Exclude x, Include y ->
          let comp = N.compare x y in
          if comp = 0 then 1 else comp
        | Include x, Exclude y ->
          let comp = N.compare x y in
          if comp = 0 then -1 else comp
        | Inf, Inf -> 0
        | Inf, _ -> -1
        | _, Inf -> 1
      ;;
    end)

  module RightBound = ExpOrder.Make (struct
      type t = Bound.t

      let compare x y =
        match x, y with
        | Exclude x, Exclude y | Include x, Include y -> N.compare x y
        | Exclude x, Include y ->
          let comp = N.compare x y in
          if comp = 0 then -1 else comp
        | Include x, Exclude y ->
          let comp = N.compare x y in
          if comp = 0 then 1 else comp
        | Inf, Inf -> 0
        | Inf, _ -> 1
        | _, Inf -> -1
      ;;
    end)

  type t =
    | Bound of bound * bound
    | Empty
  [@@deriving sexp]

  let normalize i =
    let pass =
      match i with
      | Bound (Include x, Include y) -> N.compare x y <= 0
      | Bound (Include x, Exclude y)
      | Bound (Exclude x, Include y)
      | Bound (Exclude x, Exclude y) -> N.compare x y < 0
      | _ -> true
    in
    if pass then i else Empty
  ;;

  let make_include left right = normalize (Bound (Include left, Include right))
  let make_exclude left right = normalize (Bound (Exclude left, Exclude right))
  let return n = Bound (Include n, Include n)
  let pinf left = Bound (Include left, Inf)
  let ninf right = Bound (Inf, Include right)
  let pinf_strict left = Bound (Exclude left, Inf)
  let ninf_strict right = Bound (Inf, Exclude right)
  let inf = Bound (Inf, Inf)

  let destr = function
    | Bound (a, b) -> Some (a, b)
    | Empty -> None
  ;;

  let empty = Empty

  let inter x y =
    match x, y with
    | Bound (a, b), Bound (c, d) ->
      let left = LeftBound.max a c
      and right = RightBound.min b d in
      normalize @@ Bound (left, right)
    | _ -> Empty
  ;;

  let subset x y =
    match x, y with
    | Bound (a, b), Bound (c, d) -> LeftBound.more_eq a c && RightBound.less_eq b d
    | Empty, _ -> true
    | _, Empty -> false
  ;;

  let compare x y =
    if x = y
    then 0
    else if subset x y
    then -1
    else if subset y x
    then 1
    else failwith "incomparable intervals"
  ;;

  let is_empty = function
    | Empty -> true
    | _ -> false
  ;;

  let contains i n = subset (return n) i

  let shift_by i n =
    match i with
    | Bound (a, b) -> Bound (Bound.(shift_by a n), Bound.(shift_by b n))
    | Empty -> Empty
  ;;

  let complement_left = function
    | Bound (left, _) ->
      let* bound = Bound.neg left in
      Some (Bound (Inf, bound))
    | Empty -> Some (Bound (Inf, Inf))
  ;;

  let complement_right = function
    | Bound (_, right) ->
      let* bound = Bound.neg right in
      Some (Bound (bound, Inf))
    | Empty -> Some (Bound (Inf, Inf))
  ;;

  let ( <-> ) x y = normalize @@ Bound (Exclude x, Exclude y)
  let ( =-> ) x y = normalize @@ Bound (Include x, Exclude y)
  let ( <-= ) x y = normalize @@ Bound (Exclude x, Include y)
  let ( =-= ) x y = normalize @@ Bound (Include x, Include y)
end

let%test_module _ =
  (module struct
    module II : I with type num = int = Make (Number.Integer)

    let%test_unit _ =
      [%test_eq: II.t] (II.make_include ~-1 1) (II.inter (II.pinf ~-1) (II.ninf 1))
    ;;

    let%test _ = II.subset (II.make_include ~-1 1) II.inf
    let%test _ = II.contains II.inf 0
    let%test _ = II.contains (II.pinf 0) 0
    let%test _ = II.contains (II.ninf 0) 0
    let%test_unit _ = [%test_eq: II.t] (II.inter (II.ninf 0) (II.pinf 0)) (II.return 0)

    let%test_unit _ =
      [%test_eq: II.t]
        (II.inter (II.make_include ~-1 1) (II.make_include 0 2))
        (II.make_include 0 1)
    ;;

    let%test_unit _ =
      [%test_eq: II.t] (II.inter (II.ninf_strict 0) (II.pinf_strict 0)) II.empty
    ;;

    let%test_unit _ = [%test_eq: II.t] II.(0 <-= 0) II.empty
    let%test_unit _ = [%test_eq: II.t] II.(0 =-> 0) II.empty
    let%test_unit _ = [%test_eq: II.t] II.(0 <-> 0) II.empty
  end)
;;
