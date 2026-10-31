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
  let bins_cardinal m = Bins.cardinal m
  let sample_cardinal m = Bins.fold (fun _ freq sum -> freq + sum) m 0
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
  val bins_cardinal : t -> int
  val sample_cardinal : t -> int
end

let write (module F : S) ch histogram =
  let ch = Csv.to_channel ch in
  Csv.output_record ch [ F.column_name; frequency_column_name ];
  ignore
  @@ F.fold
       (fun bin freq ch ->
          Csv.output_record ch [ F.bin_to_string bin; Integer.to_string freq ];
          ch)
       histogram
       ch
;;

let load (module F : S) ch =
  let ch = Csv.of_channel ~has_header:true ch in
  let header = Csv.Rows.header ch in
  if header = []
  then failwith "Frequency.load: no header"
  else
    Csv.Rows.fold_left
      ~f:(fun hist row ->
        let bin = F.bin_of_string @@ Csv.Row.find row F.column_name in
        let freq = Integer.of_string @@ Csv.Row.find row frequency_column_name in
        (* very thin moment: in case the bin numbers are not saved exactly (rationals->decimals), F.insert would rewrite the values, thus we use F.add here *)
        F.add bin freq hist)
      ~init:F.empty
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

let mean (module F : S) (module N : MeanN with type bin = F.bin) hist =
  let sum, n =
    F.fold
      (fun bin freq (sum, n) ->
         let samples_sum = N.mul (N.of_bin bin) (N.of_int freq) in
         N.add samples_sum sum, n + freq)
      hist
      (N.zero, 0)
  in
  N.div sum (N.of_int n)
;;

let std (module F : S) (module N : STDN with type bin = F.bin) ~mean:mean_value hist =
  let module N = struct
    include N

    let of_bin x = N.pow2 (N.sub (N.of_bin x) mean_value)
  end
  in
  N.sqrt (mean (module F) (module N) hist)
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

module InvCDF = struct
  module Exact = struct
    type 'n t =
      | CDF of
          { cum_freq : (int * 'n) array (** Invariant: array is not empty *)
          ; total : int
          }

    module type N = sig
      type t

      val zero : t
    end

    (* TODO: I am not sure it is correct, the cdf like this does not have the lower bound. *)
    let of_freq (module F : S) (module N : N with type t = F.bin) freqs =
      let size = F.bins_cardinal freqs in
      let cum_freq = Array.make size (0, N.zero) in
      let _, total =
        F.fold
          (fun bin freq (i, total) ->
             let total = total + freq in
             Array.set cum_freq i (total, bin);
             Int.succ i, total)
          freqs
          (0, 0)
      in
      CDF { cum_freq; total }
    ;;

    let linear_rvs (CDF { cum_freq; total }) =
      let choice = Random.int total in
      let value =
        Array.find_mapi
          (fun i (threshhold, value) ->
             if Integer.less_eq choice threshhold then Some (i, value) else None)
          cum_freq
      in
      Option.unwrap ~expect:"InvCDF.linear_rvs: value should always be picked" value
    ;;

    let binary_rvs (CDF { cum_freq; total }) =
      let choice = Random.int total in
      let len = Array.length cum_freq in
      (* Assumes that the rates of values are relatively the same, so ratio between total and array is roughtly preserved between a guess and array index *)
      let guess_index = len * choice / total in
      let threshhold, guess = Array.get cum_freq guess_index in
      let rec go_down guess_index value =
        let new_index = Int.pred guess_index in
        if Integer.equal new_index 0
        then guess_index, value
        else (
          let threshhold, new_value = Array.get cum_freq new_index in
          if Integer.less_eq threshhold choice
          then go_down new_index new_value
          else guess_index, value)
      in
      let rec go_up i =
        let threshhold, value = Array.get cum_freq i in
        if Integer.less_eq choice threshhold then i, value else go_up (Int.succ i)
      in
      if Integer.less_eq choice threshhold
      then go_down guess_index guess
      else go_up (Int.succ guess_index)
    ;;

    let with_width = ()
  end

  (** Polynomial CDF. *)
  module Poly = struct
    type 'n t = Polynome of 'n array
  end

  (** Finite probability precision. *)
  module FPP = struct
    type 'n t = FPP of 'n array

    (* let of_exact ~precision Exact.(CDF {cum_freq;total}) =  *)
  end
end
