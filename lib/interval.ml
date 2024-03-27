module type I = sig
  type t
  type num

  val make : num -> num -> t
  val pinf : num -> t
  val ninf : num -> t
  val inf : t
  val destr : t -> num option * num option
  val inter : t -> t -> t
  val subset : t -> t -> bool
  val compare : t -> t -> int
  val is_empty : t -> bool

  include Sexplib0.Sexpable.S with type t := t
end

module type Num = sig
  include Set.OrderedType
  include Sexplib0.Sexpable.S with type t := t
end

module Make (N : Num) : I with type num := N.t = struct
  open Sexplib0.Sexp_conv

  module LeftBound = Misc.MakeCompare (struct
      type t = N.t option

      let compare x y =
        match x, y with
        | None, None -> 0
        | Some _, None -> -1
        | None, Some _ -> 1
        | Some x, Some y -> -N.compare x y
      ;;
    end)

  module RightBound = Misc.MakeCompare (struct
      type t = N.t option

      let compare x y =
        match x, y with
        | None, None -> 0
        | Some _, None -> -1
        | None, Some _ -> 1
        | Some x, Some y -> N.compare x y
      ;;
    end)

  type t = N.t option * N.t option [@@deriving sexp]

  let make left right =
    if N.compare left right = 1
    then invalid_arg "left bound bigger than right"
    else Some left, Some right
  ;;

  let pinf left = Some left, None
  let ninf right = None, Some right
  let inf = None, None
  let destr (a, b) = a, b
  let inter (a, b) (c, d) = min a c, min b d
  let subset (a, b) (c, d) = LeftBound.less_eq a c && RightBound.less_eq b d

  let compare (a, b) (c, d) =
    let r1 = LeftBound.compare a b in
    let r2 = RightBound.compare c d in
    if r1 * r2 >= 0 then r1 * r2 else failwith "incomparable intervals"
  ;;

  let is_empty = function
    | Some x, Some y -> x = y
    | _ -> false
  ;;
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
  end)
;;
