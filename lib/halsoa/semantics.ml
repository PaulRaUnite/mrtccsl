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

open Mrtccsl.Language
open Specification.Builder

let of_bounded_dist ~builder v { bounds = a, b; dist } =
  duration builder @@ NumRelation (v, `LessEq, Const b);
  duration builder @@ NumRelation (v, `MoreEq, Const a);
  probab builder @@ ContinuousProcess { name = v; dist }
;;

(*TODO: think about moving the constraint declarations into effects or at least monad.*)

let of_policy ~builder name trigger policy =
  let jitter_var = jitter_var name in
  match policy with
  | `AbsoluteTimer (period, bound_dist, offset) ->
    logical builder
    @@ AbsPeriodic
         { out = trigger; period; error = var jitter_var; offset = Const offset };
    of_bounded_dist ~builder jitter_var bound_dist
  | `CumulativeTimer (period, bound_dist, offset) ->
    logical builder
    @@ CumulPeriodic
         { out = trigger; period; error = var jitter_var; offset = Const offset };
    of_bounded_dist ~builder jitter_var bound_dist
  | `Signal signal -> logical builder @@ Coincidence [ signal_receive signal; trigger ]
;;

let of_signal ~builder name s =
  let task_name = signal_task name in
  let start = start task_name in
  let finish = finish task_name in
  let latency_var = latency_var task_name in
  let latency =
    match s with
    | Sensor { policy; latency; as_device } ->
      of_policy ~builder task_name (if as_device then start else finish) policy;
      logical builder @@ Coincidence [ finish; signal_emit name ];
      latency
    | Actuator { policy; latency } ->
      of_policy ~builder task_name start policy;
      latency
  in
  logical builder @@ RTdelay { out = finish; arg = start; delay = var latency_var };
  of_bounded_dist ~builder latency_var latency
;;

let of_service ~builder { name; inputs = _; outputs; execution_time; policy } =
  let execution_var = exec_var name
  and trigger = trigger name
  and start = start name
  and finish = finish name in
  of_policy ~builder name trigger policy;
  logical builder @@ RTdelay { out = finish; arg = start; delay = var execution_var };
  logical builder @@ Coincidence (finish :: List.map signal_emit outputs);
  of_bounded_dist ~builder execution_var execution_time
;;

let of_component ~builder { services } =
  services |> List.to_seq |> Seq.iter (fun s -> of_service ~builder s)
;;

let rigid_scheduling ~builder name =
  let trigger = trigger name
  and start = start name in
  logical builder @@ Coincidence [ trigger; start ]
;;

let relaxed_scheduling ~builder name =
  let trigger = trigger name
  and start = start name in
  logical builder @@ Causality { cause = trigger; conseq = start }
;;

(*FIXME: it is possible that the rtdelay queue does not respect the order between the ticks and so it WILL deadlock. *)
let instant_communication ~builder signal =
  logical builder @@ Coincidence [ signal_emit signal; signal_receive signal ]
;;

let delayed_communication ~builder latency signal =
  let delay = latency_var signal in
  of_bounded_dist ~builder delay latency;
  logical builder
  @@ RTdelay { out = signal_receive signal; arg = signal_emit signal; delay = var delay }
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

let schedule_on_cpu ~builder cores components =
  let pairs =
    components
    |> List.to_seq
    |> Seq.flat_map (fun { services } ->
      services |> List.to_seq |> Seq.map (fun { name; _ } -> start name, finish name))
  in
  logical builder @@ Pool (cores, List.of_seq pairs)
;;

(*TODO: implement monitors*)
(*TODO: use monitors for deadlines*)
(*TODO: implement extraction of tasks for svgbob*)
let of_system ~relaxed_sched ?delayed_comm ?cores ((components, hal) : _ system) builder =
  hal |> Hashtbl.to_seq |> Seq.iter (Tuple.fn2 (of_signal ~builder));
  components |> List.to_seq |> Seq.iter (of_component ~builder);
  let shedule_service = if relaxed_sched then relaxed_scheduling else rigid_scheduling in
  components
  |> List.to_seq
  |> Seq.iter (fun { services } ->
    services |> List.to_seq |> Seq.iter (fun { name; _ } -> shedule_service ~builder name));
  let comm_pattern =
    match delayed_comm with
    | Some latency -> delayed_communication latency
    | None -> instant_communication
  in
  system_signals (components, hal) |> Seq.iter (comm_pattern ~builder);
  match cores with
  | Some cores -> schedule_on_cpu ~builder cores components
  | None -> ()
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
  let open Mrtccsl.Analysis.FunctionalChain.Chain in
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
    [ { first = start st; rest = [ `Causality, finish st ]; periodic = true }, [ signal ]
    ]
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
