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
  val constant_bounds : t -> (num * num) option
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
  val complement_left : t -> t option
  val complement_right : t -> t option
  val left_bound_opt : t -> num option
  val right_bound_opt : t -> num option
  val is_left_unbound : t -> bool
  val is_right_unbound : t -> bool
  val is_any_unbound : t -> bool

  include Sexplib0.Sexpable.S with type t := t
end

module type Num = sig
  include Set.OrderedType
  include Sexplib0.Sexpable.S with type t := t

  val ( + ) : t -> t -> t
end

module Make (N : Num) : I with type num = N.t = struct
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

  module LeftBound = Interface.ExpOrder.Make (struct
      type t = Bound.t

      let[@inline always] compare x y =
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

  module RightBound = Interface.ExpOrder.Make (struct
      type t = Bound.t

      let[@inline always] compare x y =
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

  let[@inline always] normalize i =
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

  let constant_bounds = function
    | Bound (Include x, Include y) -> Some (x, y)
    | _ -> None
  ;;

  let empty = Empty

  let[@inline always] inter x y =
    match x, y with
    | Bound (a, b), Bound (c, d) ->
      let left = LeftBound.max a c
      and right = RightBound.min b d in
      normalize @@ Bound (left, right)
    | _ -> Empty
  ;;

  (**[subset x y] returns true when [y] contains [x].*)
  let[@inline always] subset x y =
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

  let[@inline always] is_empty = function
    | Empty -> true
    | _ -> false
  ;;

  (**[contains i n] returns either element [n] is in interval [i].*)
  let[@inline always] contains i n = subset (return n) i

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

  let is_left_unbound = function
    | Bound (Inf, _) -> true
    | _ -> false
  ;;

  let is_right_unbound = function
    | Bound (_, Inf) -> true
    | _ -> false
  ;;

  let left_bound_opt = function
    | Bound ((Exclude x | Include x), _) -> Some x
    | _ -> None
  ;;

  let right_bound_opt = function
    | Bound (_, (Exclude x | Include x)) -> Some x
    | _ -> None
  ;;

  let is_any_unbound interval = is_left_unbound interval || is_right_unbound interval
end

module MakeDebug (N : sig
    include Num

    val to_string : t -> string
  end) =
struct
  include Make (N)

  let to_string = function
    | Bound (l, r) ->
      let l =
        match l with
        | Include b -> Printf.sprintf "[%s" (N.to_string b)
        | Exclude b -> Printf.sprintf "(%s" (N.to_string b)
        | Inf -> "(-∞"
      in
      let r =
        match r with
        | Include b -> Printf.sprintf "%s]" (N.to_string b)
        | Exclude b -> Printf.sprintf "%s)" (N.to_string b)
        | Inf -> "+∞)"
      in
      Printf.sprintf "%s,%s" l r
    | Empty -> "∅"
  ;;
end

let%test_module _ =
  (module struct
    module II = Make (Number.Integer)
    open II

    let%test_unit _ = [%test_eq: t] (-1 =-= 1) (inter (pinf (-1)) (ninf 1))
    let%test _ = subset (-1 =-= 1) inf
    let%test _ = subset (0 =-= 1) (0 =-= 2)
    let%test _ = contains inf 0
    let%test _ = contains (pinf 0) 0
    let%test _ = contains (ninf 0) 0
    let%test_unit _ = [%test_eq: t] (inter (ninf 0) (pinf 0)) (return 0)
    let%test_unit _ = [%test_eq: t] (inter (-1 =-= 1) (0 =-= 2)) (0 =-= 1)
    let%test_unit _ = [%test_eq: t] (inter (ninf_strict 0) (pinf_strict 0)) empty
    let%test_unit _ = [%test_eq: t] (0 <-= 0) empty
    let%test_unit _ = [%test_eq: t] (0 =-> 0) empty
    let%test_unit _ = [%test_eq: t] (0 <-> 0) empty
  end)
;;
