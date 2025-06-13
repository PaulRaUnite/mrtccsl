open Prelude
open Definition

let start = Printf.sprintf "%s.s"
let finish = Printf.sprintf "%s.f"
let trigger = Printf.sprintf "%s.t"
let deadline = Printf.sprintf "%s.d"
let exec_var = Printf.sprintf "%s@et"
let period_var = Printf.sprintf "%s@p"
let latency_var = Printf.sprintf "%s@l"
let jitter_var = Printf.sprintf "%s@j"
let signal_emit = Printf.sprintf "%s.e"
let signal_receive = Printf.sprintf "%s.r"
let signal_task = Printf.sprintf "oem.%s"

open Mrtccsl.Rtccsl

let bounds_to_rel v (a, b) =
  [ TimeVarRelation (v, LessEq, Const b); TimeVarRelation (v, MoreEq, Const a) ]
;;

(*TODO: think about moving the constraint declarations into effects or at least monad.*)

let of_policy name trigger =
  let period_var = period_var name in
  let jitter_var = jitter_var name in
  function
  | `AbsoluteTimer (period, { bounds; dist }, offset) ->
    ( [ jitter_var, dist ]
    , { constraints =
          [ AbsPeriodic
              { out = trigger
              ; period = Const period
              ; error = jitter_var
              ; offset = Const offset
              }
          ]
      ; var_relations = bounds_to_rel jitter_var bounds
      } )
  | `CumulativeTimer ({ bounds; dist }, offset) ->
    ( [ period_var, dist ]
    , { constraints =
          [ CumulPeriodic { out = trigger; period = period_var; offset = Const offset } ]
      ; var_relations = bounds_to_rel period_var bounds
      } )
  | `Signal signal ->
    [], constraints_only [ Coincidence [ signal_receive signal; trigger ] ]
;;

let of_signal name s =
  let task_name = signal_task name in
  let start = start task_name in
  let finish = finish task_name in
  let latency_var = latency_var task_name in
  let (policy_dist, policy_spec), latency =
    match s with
    | Sensor { policy; latency; as_device } ->
      let dist, spec = of_policy task_name (if as_device then start else finish) policy in
      let spec =
        { constraints =
            Coincidence [ finish; signal_emit name ] :: spec.constraints
            (*TODO: replace with probabilistic subclocking in the future?*)
        ; var_relations = spec.var_relations
        }
      in
      (dist, spec), latency
    | Actuator { policy; latency } -> of_policy task_name start policy, latency
  in
  let latency_dist = [ latency_var, latency.dist ] in
  let latency_spec =
    { constraints = [ RTdelay { out = finish; arg = start; delay = latency_var } ]
    ; var_relations = bounds_to_rel latency_var latency.bounds
    }
  in
  policy_dist @ latency_dist, merge policy_spec latency_spec
;;

let merge (d1, s1) (d2, s2) = d1 @ d2, merge s1 s2

let of_service { name; inputs = _; outputs; execution_time; policy } =
  let execution_var = exec_var name
  and trigger = trigger name
  and start = start name
  and finish = finish name in
  let policy = of_policy name trigger policy in
  let exec =
    ( [ execution_var, execution_time.dist ]
    , { constraints =
          [ RTdelay { out = finish; arg = start; delay = execution_var }
          ; Coincidence (finish :: List.map signal_emit outputs)
          ]
      ; var_relations = bounds_to_rel execution_var execution_time.bounds
      } )
  in
  merge policy exec
;;

let of_component { services } = services |> List.to_seq |> Seq.map (fun s -> of_service s)

let rigid_scheduling name =
  let trigger = trigger name
  and start = start name in
  constraints_only [ Coincidence [ trigger; start ] ]
;;

let relaxed_scheduling name =
  let trigger = trigger name
  and start = start name in
  constraints_only [ Causality { cause = trigger; conseq = start } ]
;;

(*FIXME: it is possible that the rtdelay queue does not respect the order between the ticks and so it WILL deadlock. *)
let instant_communication signal =
  ( []
  , { constraints = [ Coincidence [ signal_emit signal; signal_receive signal ] ]
    ; var_relations = []
    } )
;;

let delayed_communication latency signal =
  let delay = latency_var signal in
  ( [ delay, latency.dist ]
  , { constraints =
        [ RTdelay { out = signal_receive signal; arg = signal_emit signal; delay } ]
    ; var_relations = bounds_to_rel delay latency.bounds
    } )
;;

let system_signals (components, hal) : id Seq.t =
  let component_signals =
    components
    |> List.to_seq
    |> Seq.flat_map (fun { services; _ } ->
      services
      |> List.to_seq
      |> Seq.flat_map (fun { inputs; outputs; _ } ->
        Seq.append (List.to_seq inputs) (List.to_seq outputs)))
  in
  let hal_signals = hal |> Hashtbl.to_seq_keys in
  let signals =
    Seq.append component_signals hal_signals
    |> List.of_seq
    |> List.sort_uniq String.compare
  in
  List.to_seq signals
;;

let schedule_on_cpu cores components =
  let pairs =
    components
    |> List.to_seq
    |> Seq.flat_map (fun { services } ->
      services |> List.to_seq |> Seq.map (fun { name; _ } -> start name, finish name))
  in
  constraints_only [ Pool (cores, List.of_seq pairs) ]
;;

(*TODO: implement monitors*)
(*TODO: use monitors for deadlines*)
(*TODO: implement extraction of tasks for svgbob*)
let of_system ~relaxed_sched ?delayed_comm ?cores ((components, hal) : _ system) =
  let hal_specs = hal |> Hashtbl.to_seq |> Seq.map (Tuple.fn2 of_signal) in
  let component_specs = components |> List.to_seq |> Seq.flat_map of_component in
  let shedule_service = if relaxed_sched then relaxed_scheduling else rigid_scheduling in
  let scheduling =
    components
    |> List.to_seq
    |> Seq.flat_map (fun { services } ->
      services |> List.to_seq |> Seq.map (fun { name; _ } -> shedule_service name))
    |> Seq.map (fun spec -> [], spec)
  in
  let comm_pattern =
    match delayed_comm with
    | Some latency -> delayed_communication latency
    | None -> instant_communication
  in
  let communication = system_signals (components, hal) |> Seq.map comm_pattern in
  let resource_spec =
    match cores with
    | Some cores -> [], schedule_on_cpu cores components
    | None -> [], empty
  in
  let specs =
    Seq.append_list
      [ hal_specs; component_specs; scheduling; communication; Seq.return resource_spec ]
  in
  Seq.fold_left merge ([], empty) specs
;;

let system_tasks (components, hal) =
  let task = fun name -> name, trigger name, start name, finish name, deadline name in
  let signal_exec_tasks =
    hal |> Hashtbl.to_seq_keys |> Seq.map (fun name -> task (signal_task name))
  and component_tasks =
    components
    |> List.to_seq
    |> Seq.flat_map (fun c ->
      c.services |> List.to_seq |> Seq.map (fun { name; _ } -> task name))
  and signal_comm_tasks =
    hal
    |> Hashtbl.to_seq_keys
    |> Seq.map (fun name -> name, "", signal_emit name, signal_receive name, "")
  in
  [ signal_exec_tasks; component_tasks; signal_comm_tasks ]
  |> Seq.append_list
  |> List.of_seq
;;

(** Extract functional chains from signal paths. *)
let signals_to_chain (components, hal) signal_path =
  let open Mrtccsl.Analysis.FunctionalChain in
  let module H = Hashtbl.Make (String) in
  let policy_to_relation = function
    | `AbsoluteTimer _ | `CumulativeTimer _ -> `Sampling
    | `Signal _ -> `Causality
  in
  let actuator_consumers =
    hal
    |> Hashtbl.to_seq
    |> Seq.filter_map (fun (signal, sig_type) ->
      match sig_type with
      | Sensor _ -> None
      | Actuator { policy; _ } ->
        Some ([ signal ], (policy_to_relation policy, signal_task signal, [])))
  in
  let component_consumers =
    components
    |> List.to_seq
    |> Seq.flat_map (fun c -> List.to_seq c.services)
    |> Seq.map (fun s -> s.inputs, (policy_to_relation s.policy, s.name, s.outputs))
  in
  let consumers =
    Seq.append actuator_consumers component_consumers |> H.Collect.by_tags
  in
  let get_sensor signal =
    (*TODO: maybe replace by using producers map so that I can support functional chains without hal? *)
    let st = signal_task signal in
    [ { first = start st; rest = [ `Causality, finish st ] }, [ signal ] ]
  in
  let candidates =
    List.fold_left
      (fun producers to_consume ->
         let producers =
           List.filter
             (fun (_, outputs) -> List.exists (String.equal to_consume) outputs)
             producers
         in
         let consumers = H.find consumers to_consume in
         List.map_cartesian
           (fun (chain, _) (instruction, task, outputs) ->
              let chain_fragment =
                [ `Causality, signal_emit to_consume
                ; `Causality, signal_receive to_consume
                ; instruction, start task
                ; `Causality, finish task
                ]
              in
              { chain with rest = List.append chain.rest chain_fragment }, outputs)
           producers
           consumers)
      (get_sensor @@ List.hd signal_path)
      signal_path
  in
  assert (List.length candidates = 1);
  let chain, _ = List.hd candidates in
  chain
;;
