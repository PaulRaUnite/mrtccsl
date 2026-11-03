(* open Prelude *)
open Prelude

module Discrete = struct
  include Frequency.Discrete

  let load = Frequency.load (module Frequency.Discrete)
end

module type N = sig
  type t

  val modulo_floor : t -> divisor:t -> int * t * t
  val zero : t
  val add : t -> t -> t
  val random : t -> t -> t
  val compare : t -> t -> int
end

exception FileNotFound of string

module Binned (F : Frequency.S) (N : N with type t = F.bin) = struct
  type t =
    | Normalized of
        { resolution : N.t
        ; freqs : F.t
        }

  let normalize_bin ~resolution bin =
    let _, bin, _ = N.modulo_floor ~divisor:resolution bin in
    bin
  ;;

  let empty resolution = Normalized { resolution; freqs = F.empty }

  let of_freq resolution freqs =
    let freqs = F.map (normalize_bin ~resolution) freqs in
    Normalized { resolution; freqs }
  ;;

  let load resolution ch =
    let freqs = Frequency.load (module F) ch in
    of_freq resolution freqs
  ;;

  (* let truncate = ()
  let rvs () = () *)

  module CDF = struct
    type t =
      | Mapping of
          { prob_to_sample : N.t array
          ; resolution : N.t
          }

    let make (Normalized { resolution; freqs }) =
      let total_samples = F.sample_cardinal freqs in
      let sample_map = Array.make total_samples N.zero in
      ignore
      @@ F.fold
           (fun bin freqs i ->
              let next_i = i + freqs in
              for j = i to Int.pred next_i do
                Array.set sample_map j bin
              done;
              next_i)
           freqs
           0;
      (*TODO: potential optimization, knowing GCD of frequencies should reduce the array by the gcd factor. *)
      Mapping { prob_to_sample = sample_map; resolution }
    ;;

    let rvs (Mapping { prob_to_sample; resolution }) () =
      let i = Random.int (Array.length prob_to_sample) in
      let sub_bin = N.random N.zero resolution in
      let bin = Array.get prob_to_sample i in
      N.add bin sub_bin
    ;;

    let load filename resolution =
      let freqs =
        try load resolution (open_in filename) with
        | Not_found -> raise (FileNotFound filename)
      in
      make freqs
    ;;

    let filter lower upper (Mapping { resolution; prob_to_sample }) =
      let prob_to_sample =
        Array.of_list
        @@ List.rev
        @@ Array.fold_left
             (fun l bin ->
                if N.compare lower bin > 1 || N.compare N.(add bin resolution) upper > 1
                then l
                else bin :: l)
             []
             prob_to_sample
      in
      Mapping { resolution; prob_to_sample }
    ;;
  end
end
