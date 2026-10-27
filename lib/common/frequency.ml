open Prelude
open Number

module Make (Bins : Map.S) = struct
  type t = int Bins.t
  type bin = Bins.key

  let sum total1 total2 = Bins.union (fun _ t1 t2 -> Some (t1 + t2)) total1 total2
  let insert = Bins.add
  let add k freq m = Bins.entry ~default:0 (Int.add freq) k m
  let empty = Bins.empty
  let fold = Bins.fold
  let map f m = Bins.fold (fun bin freq new_hist -> add (f bin) freq new_hist) m empty
end

let frequency_column_name = "frequency"

module type S = sig
  type t
  type bin

  val empty : t
  val add : bin -> int -> t -> t
  val insert : bin -> int -> t -> t
  val sum : t -> t -> t
  val bin_to_string : bin -> string
  val bin_of_string : string -> bin
  val column_name : string
  val fold : (bin -> int -> 'acc -> 'acc) -> t -> 'acc -> 'acc
  val map : (bin -> bin) -> t -> t
end

let write (module H : S) ch histogram =
  let ch = Csv.to_channel ch in
  Csv.output_record ch [ H.column_name; frequency_column_name ];
  ignore
  @@ H.fold
       (fun bin freq ch ->
          Csv.output_record ch [ H.bin_to_string bin; Integer.to_string freq ];
          ch)
       histogram
       ch
;;

let load (module H : S) ch =
  let ch = Csv.of_channel ~has_header:true ch in
  let header = Csv.Rows.header ch in
  if header = []
  then failwith "Histogram.load: no header"
  else
    Csv.Rows.fold_left
      ~f:(fun hist row ->
        let bin = H.bin_of_string @@ Csv.Row.find row H.column_name in
        let freq = Integer.of_string @@ Csv.Row.find row frequency_column_name in
        (* very thin moment: in case the bin numbers are not saved exactly (rationals->decimals), H.insert would rewrite the values, thus we use H.add here *)
        H.add bin freq hist)
      ~init:H.empty
      ch
;;

module type MeanN = sig
  include Interface.Number.Field

  type bin

  val of_int : int -> t
  val of_bin : bin -> t
end

module type STDN = sig
  include MeanN

  val pow2 : t -> t
  val sqrt : t -> t
end

let mean (module H : S) (module N : MeanN with type bin = H.bin) hist =
  let sum, n =
    H.fold
      (fun bin freq (sum, n) ->
         let samples_sum = N.mul (N.of_bin bin) (N.of_int freq) in
         N.add samples_sum sum, n + freq)
      hist
      (N.zero, 0)
  in
  N.div sum (N.of_int n)
;;

let std (module H : S) (module N : STDN with type bin = H.bin) ~mean:mean_value hist =
  let module N = struct
    include N

    let of_bin x = N.pow2 (N.sub (N.of_bin x) mean_value)
  end
  in
  N.sqrt (mean (module H) (module N) hist)
;;

module Discrete = struct
  module Bins = Map.Make (Integer)
  include Make (Bins)

  let column_name = "bin(Z)"
  let bin_to_string = Integer.to_string
  let bin_of_string = Integer.of_string

  module STDN = struct
    include Float

    type bin = Bins.key

    let of_bin = of_int
  end
end

module ContinuousDecimal = struct
  module Bins = Map.Make (Rational)
  include Make (Bins)

  let column_name = "bin(Z.N)"
  let bin_to_string = Rational.to_string
  let bin_of_string = Rational.of_string

  module STDN = struct
    include Float

    type bin = Bins.key

    let of_bin = Rational.to_float
  end
end

module ContinuousExact = struct
include ContinuousDecimal

  let column_name = "bin(Q)"
  let bin_to_string = Rational.to_exact_string
  let bin_of_string = Rational.of_exact_string
end
