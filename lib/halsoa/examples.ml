open Prelude
open Definition
open Mrtccsl.Automata.Simple

module type Num = sig
  include Mrtccsl.Simple.Num

  val ( / ) : t -> t -> t
  val of_int : int -> t
end

(*TODO: move to JSON or something, this is ridiculous *)
module Make (N : Num) = struct
  open N

  let sigma n (l, r) =
    let dev = (r - l) / of_int (Int.mul 2 n) in
    let mean = l + ((r - l) / of_int 2) in
    (* Printf.printf "mean: %s dev:%s\n" (N.to_string mean) (N.to_string dev); *)
    Normal { mean; dev }
  ;;

  let range_to_bound_dist ~n_sigma bounds = { bounds; dist = sigma n_sigma bounds }

  type 'n aebsimple_config =
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

  let make_periodic_policy ~absolute ~n_sigma range offset =
    if absolute
    then (
      let l, r = range in
      let jitter = (r - l) / of_int 2 in
      let period = l + jitter in
      `AbsoluteTimer (period, range_to_bound_dist ~n_sigma (N.neg jitter, jitter), offset))
    else `CumulativeTimer (range_to_bound_dist ~n_sigma range, offset)
  ;;

  let aebsimple_template
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
    let components =
      [ { services =
            [ { name = "aeb.control"
              ; inputs = [ "radar" ]
              ; outputs = [ "brake" ]
              ; execution_time = range_to_bound_dist ~n_sigma controller_exec_time
              ; policy = `Signal "radar"
              }
            ]
        }
      ]
    and hal =
      [ ( "radar"
        , Sensor
            { as_device = true
            ; policy =
                make_periodic_policy
                  ~absolute
                  ~n_sigma
                  sensor_sampling_period
                  sensor_offset
            ; latency = range_to_bound_dist ~n_sigma sensor_latency
            } )
      ; ( "brake"
        , Actuator
            { policy =
                make_periodic_policy
                  ~absolute
                  ~n_sigma
                  actuator_sampling_period
                  actuator_offset
            ; latency = range_to_bound_dist ~n_sigma actuator_latency
            } )
      ]
      |> List.to_seq
      |> Hashtbl.of_seq
    in
    components, hal
  ;;

  let useless_def_spec chain =
    let open Mrtccsl.Analysis.FunctionalChain in
    let open Mrtccsl.Rtccsl in
    let constraints, _ =
      List.fold_left
        (fun (spec, prev) -> function
           | `Sampling, c ->
             let useful = Printf.sprintf "%s++" c
             and useless = Printf.sprintf "%s--" c in
             ( List.append
                 [ Sample { out = useful; arg = prev; base = c }
                 ; Minus { out = useless; arg = c; except = [ useful ] }
                 ]
                 spec
             , c )
           | `Causality, c -> spec, c)
        ([], chain.first)
        chain.rest
    in
    Mrtccsl.Rtccsl.constraints_only constraints
  ;;

  let of_sys ?cores ?delayed_comm ~n_sigma ~relaxed_sched sys chain =
    let dist, spec =
      Semantics.of_system
        ~relaxed_sched
        ?delayed_comm:(Option.map (range_to_bound_dist ~n_sigma) delayed_comm)
        ?cores
        sys
    in
    let tasks = Semantics.system_tasks sys in
    dist, Mrtccsl.Rtccsl.merge spec (useless_def_spec chain), tasks
  ;;

  let of_aebsimple_config c =
    let c = map_aebsimple_config of_int c in
    let { name; n_sigma; relaxed_sched; delayed_comm; cores; _ } = c in
    let sys = aebsimple_template c in
    let chain = Semantics.signals_to_chain sys [ "radar"; "brake" ] in
    let dist, spec, tasks =
      of_sys ?cores ~n_sigma ?delayed_comm ~relaxed_sched sys chain
    in
    name, dist, spec, tasks, chain
  ;;

  let aebsimple_variants =
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
    ; { name = "c5"
      ; n_sigma = 2
      ; absolute = false
      ; sensor_sampling_period = 14, 16
      ; sensor_latency = 1, 3
      ; sensor_offset = 0
      ; controller_exec_time = 2, 4
      ; actuator_sampling_period = 4, 6
      ; actuator_latency = 1, 3
      ; actuator_offset = 0
      ; relaxed_sched = false
      ; delayed_comm = None
      ; cores = None
      }
    ]
    |> List.map of_aebsimple_config
  ;;

  type 'n aebs_config =
    { n_sigma : int
    ; camera_offset : 'n
    ; lidar_offset : 'n
    ; radar_offset : 'n
    ; fusion_offset : 'n
    ; brake_offset : 'n
    ; relaxed_sched : bool
    ; delayed_comm : ('n * 'n) option
    ; cores : int option
    }
  [@@deriving map]

  let aebsfull_template
        { n_sigma : int
        ; camera_offset
        ; lidar_offset
        ; radar_offset
        ; fusion_offset
        ; brake_offset
        ; relaxed_sched
        ; delayed_comm
        ; cores : int option
        }
    =
    let of_range = Tuple.map2 N.of_int in
    let range_to_bound_dist ~n_sigma range =
      range_to_bound_dist ~n_sigma @@ of_range range
    in
    let make_periodic_policy ~absolute ~n_sigma range offset =
      make_periodic_policy ~absolute ~n_sigma (of_range range) (N.of_int offset)
    in
    let sensor_period = 14, 16 in
    let sensor_ex_time = 1, 3 in
    let fusion_period = 6, 8 in
    let fusion_ex_time = 4, 6 in
    let controller_ex_time = 6, 10 in
    let actuator_ex_time = 1, 3 in
    let brake_period = 4, 6 in
    let absolute = true in
    let components =
      [ { services =
            [ { name = "aebs.fusion"
              ; inputs = [ "radar"; "camera"; "lidar" ]
              ; outputs = [ "fused_map" ]
              ; execution_time = range_to_bound_dist ~n_sigma fusion_ex_time
              ; policy =
                  make_periodic_policy ~absolute ~n_sigma fusion_period fusion_offset
              }
            ; { name = "aebs.control"
              ; inputs = [ "fused_map" ]
              ; outputs = [ "brake"; "alarm" ]
              ; execution_time = range_to_bound_dist ~n_sigma controller_ex_time
              ; policy = `Signal "fused_map"
              }
            ]
        }
      ]
    and hal =
      [ ( "radar"
        , Sensor
            { as_device = true
            ; policy = make_periodic_policy ~absolute ~n_sigma sensor_period radar_offset
            ; latency = range_to_bound_dist ~n_sigma sensor_ex_time
            } )
      ; ( "camera"
        , Sensor
            { as_device = true
            ; policy = make_periodic_policy ~absolute ~n_sigma sensor_period camera_offset
            ; latency = range_to_bound_dist ~n_sigma sensor_ex_time
            } )
      ; ( "lidar"
        , Sensor
            { as_device = true
            ; policy = make_periodic_policy ~absolute ~n_sigma sensor_period lidar_offset
            ; latency = range_to_bound_dist ~n_sigma sensor_ex_time
            } )
      ; ( "brake"
        , Actuator
            { policy = make_periodic_policy ~absolute ~n_sigma brake_period brake_offset
            ; latency = range_to_bound_dist ~n_sigma actuator_ex_time
            } )
      ; ( "alarm"
        , Actuator
            { policy = `Signal "alarm"
            ; latency = range_to_bound_dist ~n_sigma actuator_ex_time
            } )
      ]
      |> List.to_seq
      |> Hashtbl.of_seq
    in
    let name =
      Printf.sprintf
        "c{c=%i,l=%i,r=%i,f=%i,b=%i}"
        camera_offset
        lidar_offset
        radar_offset
        fusion_offset
        brake_offset
    in
    let chain =
      Semantics.signals_to_chain (components, hal) [ "radar"; "fused_map"; "brake" ]
    in
    let dist, spec, tasks =
      of_sys
        ?cores
        ~n_sigma
        ?delayed_comm:(Option.map of_range delayed_comm)
        ~relaxed_sched
        (components, hal)
        chain
    in
    name, dist, spec, tasks, chain
  ;;

  let aebsfull_variants =
    let step = 3 in
    [ Seq.int_seq ~step 15
    ; Seq.int_seq ~step 15
    ; Seq.int_seq ~step 15
    ; Seq.int_seq ~step 7
    ; Seq.int_seq ~step 5
    ]
    |> List.to_seq
    |> Seq.product_seq
    |> Seq.map Seq.to_tuple5
    |> Seq.map
         (fun (camera_offset, lidar_offset, radar_offset, fusion_offset, brake_offset) ->
            aebsfull_template
              { n_sigma = 3
              ; camera_offset
              ; lidar_offset
              ; radar_offset
              ; fusion_offset
              ; brake_offset
              ; relaxed_sched = false
              ; delayed_comm = None
              ; cores = None
              })
    |> List.of_seq
  ;;
end
