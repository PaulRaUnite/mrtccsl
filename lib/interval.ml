open Prelude

module type I = sig
  type t
  type num

  val make : num -> num -> t
  val return : num -> t
  val pinf : num -> t
  val ninf : num -> t
  val inf : t
  val destr : t -> num option * num option
  val inter : t -> t -> t

  (**x is subset of y**)
  val subset : t -> t -> bool

  val compare : t -> t -> int
  val is_empty : t -> bool

  (**does interval contains a value**)
  val contains : t -> num -> bool

  include Sexplib0.Sexpable.S with type t := t
end

module type Num = sig
  include Set.OrderedType
  include Sexplib0.Sexpable.S with type t := t
end

module Make (N : Num) = struct
  type num = N.t

  open Sexplib0.Sexp_conv

  module LeftBound = ExpOrder.Make (struct
      type t = N.t option

      let compare x y =
        match x, y with
        | None, None -> 0
        | Some _, None -> 1
        | None, Some _ -> -1
        | Some x, Some y -> N.compare x y
      ;;
    end)

  module RightBound = ExpOrder.Make (struct
      type t = N.t option

      let compare x y =
        match x, y with
        | None, None -> 0
        | Some _, None -> -1
        | None, Some _ -> 1
        | Some x, Some y -> N.compare x y
      ;;
    end)

  type t =
    | Bound of N.t option * N.t option
    | Empty
  [@@deriving sexp]

  let make left right =
    if N.compare left right > 0 then Empty else Bound (Some left, Some right)
  ;;

  let return n = Bound (Some n, Some n)
  let pinf left = Bound (Some left, None)
  let ninf right = Bound (None, Some right)
  let inf = Bound (None, None)

  let destr = function
    | Bound (a, b) -> Some (a, b)
    | Empty -> None
  ;;

  let normalize i =
    match i with
    | Bound (Some x, Some y) ->
      if N.compare x y <= 0 then Bound (Some x, Some y) else Empty
    | _ -> i
  ;;

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
end

let%test_module _ =
  (module struct
    module II = Make (struct
        include Int

        let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_int
        let t_of_sexp = Sexplib0.Sexp_conv.int_of_sexp
      end)

    let%test_unit _ =
      [%test_eq: II.t] (II.make ~-1 1) (II.inter (II.pinf ~-1) (II.ninf 1))
    ;;

    let%test _ = II.subset (II.make ~-1 1) II.inf
    let%test _ = II.contains II.inf 0
    let%test _ = II.contains (II.pinf 0) 0
    let%test _ = II.contains (II.ninf 0) 0
    let%test_unit _ = [%test_eq: II.t] (II.inter (II.ninf 0) (II.pinf 0)) (II.return 0)

    let%test_unit _ =
      [%test_eq: II.t] (II.inter (II.make ~-1 1) (II.make 0 2)) (II.make 0 1)
    ;;
  end)
;;
