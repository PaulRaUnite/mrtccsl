(* open Prelude *)
open Number

module Discrete = struct
  include Frequency.Discrete

  let load = Frequency.load (module Frequency.Discrete)
end

module Binned (F : Frequency.S with type bin = Rational.t) = struct
  type t =
    | Normalized of
        { resolution : Rational.t
        ; freqs : F.t
        }

  let normalize_bin ~resolution bin =
    let _, bin, _ = Rational.modulo_floor ~divisor:resolution bin in
    bin
  ;;

  let empty resolution = Normalized { resolution; freqs = F.empty }

  let load resolution ch =
    let freqs = Frequency.load (module F) ch in
    let freqs = F.map (normalize_bin ~resolution) freqs in
    Normalized { resolution; freqs }
  ;;

  (* let truncate = ()
  let rvs () = () *)
end
