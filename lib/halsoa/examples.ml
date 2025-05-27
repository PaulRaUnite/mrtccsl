open Prelude
open Domain
open Mrtccsl.Automata.Simple

module type Num = sig
  include Mrtccsl.Simple.Num

  val ( / ) : t -> t -> t
  val of_int : int -> t
end

module Make (N : Num) = struct
  open N

  let sigma n (l, r) =
    let dev = (l - r) / of_int (Int.mul 2 n) in
    let mean = (l - r) / of_int 2 in
    Normal { mean; dev }
  ;;

  let range_to_bound_dist n_sigma bounds = { bounds; dist = sigma n_sigma bounds }

  type 'n config =
    { name : string
    ; n_sigma : int
    ; absolute : bool
    ; sensor_sampling_period : 'n * 'n
    ; sensor_latency : 'n * 'n
    ; sensor_offset : 'n
    ; controller_exec_time : 'n * 'n
    ; actuator_sampling_period : 'n * 'n
    ; actuator_latency : 'n * 'n
    ; actuator_offset : 'n
    ; relaxed_sched : bool
    ; delayed_comm : ('n * 'n) option
    ; cores : int option
    }
  [@@deriving map]

  let icteri_template
        { n_sigma
        ; absolute
        ; sensor_sampling_period
        ; sensor_latency
        ; sensor_offset
        ; controller_exec_time
        ; actuator_sampling_period
        ; actuator_latency
        ; actuator_offset
        ; _
        }
    : _ system
    =
    let make_periodic_policy range offset =
      if absolute
      then (
        let l, r = range in
        let period = (r - l) / of_int 2 in
        let jitter = l - period, r - period in
        `AbsoluteTimer (period, range_to_bound_dist n_sigma jitter, offset))
      else `CumulativeTimer (range_to_bound_dist n_sigma range, offset)
    in
    let components =
      [ { services =
            [ { name = "aeb.control"
              ; inputs = [ "radar" ]
              ; outputs = [ "brake" ]
              ; execution_time = range_to_bound_dist n_sigma controller_exec_time
              ; policy = `Signal "radar"
              }
            ]
        }
      ]
    and hal =
      [ ( "radar"
        , Sensor
            { as_device = true
            ; policy = make_periodic_policy sensor_sampling_period sensor_offset
            ; latency = range_to_bound_dist n_sigma sensor_latency
            } )
      ; ( "brake"
        , Actuator
            { policy = make_periodic_policy actuator_sampling_period actuator_offset
            ; latency = range_to_bound_dist n_sigma actuator_latency
            } )
      ]
      |> List.to_seq
      |> Hashtbl.of_seq
    in
    components, hal
  ;;

  let of_config c =
    let c = map_config of_int c in
    let { name; n_sigma; relaxed_sched; delayed_comm; cores; _ } = c in
    let sys = icteri_template c in
    let dist, spec =
      Semantics.of_system
        ~relaxed_sched
        ?delayed_comm:(Option.map (range_to_bound_dist n_sigma) delayed_comm)
        ?cores
        sys
    in
    name, dist, spec
  ;;

  let icteri_configs =
    [ { name = "c1"
      ; n_sigma = 2
      ; absolute = false
      ; sensor_sampling_period = 15, 15
      ; sensor_latency = 2, 2
      ; sensor_offset = 0
      ; controller_exec_time = 5, 5
      ; actuator_sampling_period = 5, 5
      ; actuator_latency = 2, 2
      ; actuator_offset = 0
      ; relaxed_sched = false
      ; delayed_comm = None
      ; cores = None
      }
    ; { name = "c2"
      ; n_sigma = 2
      ; absolute = false
      ; sensor_sampling_period = 14, 16
      ; sensor_latency = 1, 3
      ; sensor_offset = 0
      ; controller_exec_time = 2, 8
      ; actuator_sampling_period = 4, 6
      ; actuator_latency = 1, 3
      ; actuator_offset = 0
      ; relaxed_sched = false
      ; delayed_comm = None
      ; cores = None
      }
    ; { name = "c3"
      ; n_sigma = 2
      ; absolute = false
      ; sensor_sampling_period = 14, 16
      ; sensor_latency = 1, 3
      ; sensor_offset = 0
      ; controller_exec_time = 2, 8
      ; actuator_sampling_period = 14, 16
      ; actuator_latency = 1, 3
      ; actuator_offset = 0
      ; relaxed_sched = false
      ; delayed_comm = None
      ; cores = None
      }
    ; { name = "c4"
      ; n_sigma = 2
      ; absolute = false
      ; sensor_sampling_period = 4, 6
      ; sensor_latency = 1, 3
      ; sensor_offset = 0
      ; controller_exec_time = 2, 8
      ; actuator_sampling_period = 4, 6
      ; actuator_latency = 1, 3
      ; actuator_offset = 0
      ; relaxed_sched = false
      ; delayed_comm = None
      ; cores = None
      }
    ]
    |> List.map of_config
  ;;

  let icteri_chain =
    let open Mrtccsl.Analysis.FunctionalChain in
    let open Semantics in
    let s = "radar"
    and c = "aeb.control"
    and a = "brake" in
    { first = start s
    ; rest =
        [ `Causality, finish s
        ; `Sampling, signal_emit s
        ; `Causality, signal_receive s
        ; `Causality, start c
        ; `Causality, finish c
        ; `Sampling, signal_emit a
        ; `Causality, signal_receive a
        ; `Sampling, start a
        ; `Causality, finish a
        ]
    }
  ;;
end
