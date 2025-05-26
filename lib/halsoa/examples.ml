open Prelude
open Domain
open Mrtccsl.Automata.Simple

module type Num = sig
  include Mrtccsl.Simple.Num

  val ( / ) : t -> t -> t
  val of_int : int -> t
end

module Aux (N : Num) = struct
  open N

  let sigma n (l, r) =
    let dev = (l - r) / of_int (Int.mul 2 n) in
    let mean = (l - r) / of_int 2 in
    Normal { mean; dev }
  ;;
end

module Examples = struct
  let icteri ~n_sigma ~absolute ssp sdl cet asp adl : _ system =
    let open Number.Rational in
    let open Aux (Number.Rational) in
    let range_to_bound_dist bounds = { bounds; dist = sigma n_sigma bounds } in
    let make_periodic_policy range =
      if absolute
      then (
        let l, r = range in
        let period = (r - l) / of_int 2 in
        let jitter = l - period, r - period in
        `AbsoluteTimer (period, range_to_bound_dist jitter, zero))
      else `CumulativeTimer (range_to_bound_dist range, zero)
    in
    let components =
      [ { name = "AEB"
        ; services =
            [ { name = "Control"
              ; inputs = [ "radar" ]
              ; outputs = [ "brake" ]
              ; execution_time = range_to_bound_dist cet
              ; policy = `Signal "radar"
              }
            ]
        }
      ]
    and hal =
      [ ( "radar"
        , Sensor
            { as_device = true
            ; policy = make_periodic_policy ssp
            ; latency = range_to_bound_dist sdl
            } )
      ; ( "brake"
        , Actuator
            { policy = make_periodic_policy asp; latency = range_to_bound_dist adl } )
      ]
      |> List.to_seq
      |> Hashtbl.of_seq
    in
    components, hal
  ;;

  (* let aeb_full  *)
end
