open Prelude
open Number

module type P = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
end

module type T = sig
  module Place : Interface.TotalOrder
  module Transition : Interface.TotalOrder
  module Color : P
  module Event : P
  module Probe : Interface.TotalOrder

  module Time : sig
    include P
    include Interface.Number.Ring with type t := t
  end

  type place = Place.t
  type event = Event.t
  type color = Color.t
  type transition = Transition.t
  type time = Time.t
  type probe = Probe.t
end

module Network (T : T) = struct
  open Ppx_compare_lib.Builtin
  open Ppx_sexp_conv_lib.Conv
  include T

  type place_type =
    | Variable
    | Queue

  module Coloring = struct
    include Set.Make (Color)

    let sexp_of_t = sexp_of_list Color.sexp_of_t << to_list
    let t_of_sexp = list_of_sexp Color.t_of_sexp >> of_list
  end

  type token =
    { visits : (Event.t * Time.t) list
    ; coloring : Coloring.t
    }
  [@@deriving compare, sexp]

  let empty_token = { visits = []; coloring = Coloring.empty }

  let merge_tokens { visits = v1; coloring = c1 } { visits = v2; coloring = c2 } =
    { visits = List.append v1 v2; coloring = Coloring.union c1 c2 }
  ;;

  let visit { visits; coloring } event time more_color =
    { visits = (event, time) :: visits; coloring = Coloring.union coloring more_color }
  ;;

  type inner_place =
    | Variable of token * bool
    | Queue of token list

  let read_from_place p =
    match p with
    | Variable (token, init) -> if init then Some token, p else None, p
    | Queue q ->
      let hd, tail = List.first_partition q in
      hd, Queue tail
  ;;

  let write_to_place token = function
    | Variable (_, _) -> Variable (token, true)
    | Queue q -> Queue (List.append q [ token ])
  ;;

  type inner_transition =
    { input_arcs : place list
    ; output_arcs : place list
    ; coloring : Coloring.t
    ; event : event
    }

  type color_match =
    | Any
    | Single of Color.t
    | And of color_match * color_match
    | Or of color_match * color_match
  [@@deriving compare]

  let rec check_color_match coloring = function
    | Any -> true
    | Single color -> Coloring.mem color coloring
    | And (m1, m2) -> check_color_match coloring m1 && check_color_match coloring m2
    | Or (m1, m2) -> check_color_match coloring m1 || check_color_match coloring m2
  ;;

  module Places = Map.Make (Place)
  module Transitions = Map.Make (Transition)
  module Events = Map.Make (Event)
  module Probes = Map.Make (Probe)

  type t =
    { places : inner_place Places.t
    ; transitions : inner_transition Transitions.t
    ; probes : (color_match * Transition.t) Probes.t
    }

  let empty =
    { places = Places.empty; transitions = Transitions.empty; probes = Probes.empty }
  ;;

  type error =
    | IncompatiblePlaceDefinition of place
    (** When code declares that a place is both variable and queue at the same time. *)
    | MissingTransition of transition
    | IncompatibleTransitionDefinition of transition
    | IncompatibleProbeDefinition of probe

  (** Adds variable place to the network. *)
  let add_variable id net =
    match Places.find_opt id net.places with
    | Some (Variable _) -> Ok net
    | Some _ -> Error (IncompatiblePlaceDefinition id)
    | None ->
      Ok { net with places = Places.add id (Variable (empty_token, false)) net.places }
  ;;

  (** Adds queue variable to the network. *)
  let add_queue id net =
    match Places.find_opt id net.places with
    | Some (Queue _) -> Ok net
    | Some _ -> Error (IncompatiblePlaceDefinition id)
    | None -> Ok { net with places = Places.add id (Queue []) net.places }
  ;;

  (** Adds an empty transition with an event. *)
  let add_transition id event net =
    match Transitions.find_opt id net.transitions with
    | None ->
      Ok
        { net with
          transitions =
            Transitions.add
              id
              { input_arcs = []; output_arcs = []; event; coloring = Coloring.empty }
              net.transitions
        }
    | Some t ->
      if Event.compare t.event event = 0
      then Ok net
      else Error (IncompatibleTransitionDefinition id)
  ;;

  (** Adds dependency (input arc) to a transition. All inputs need to have data in order to activate the transition. *)
  let add_dependency id source net =
    match Transitions.find_opt id net.transitions with
    | None -> Error (MissingTransition id)
    | Some t ->
      Ok
        { net with
          transitions =
            Transitions.add
              id
              { t with input_arcs = source :: t.input_arcs }
              net.transitions
        }
  ;;

  (** Adds cause (output arc) to a transition. *)
  let add_cause id target net =
    match Transitions.find_opt id net.transitions with
    | None -> Error (MissingTransition id)
    | Some t ->
      Ok
        { net with
          transitions =
            Transitions.add
              id
              { t with output_arcs = target :: t.output_arcs }
              net.transitions
        }
  ;;

  (** Adds coloring to output tokens of a transition. *)
  let inject_color at color net =
    match Transitions.find_opt at net.transitions with
    | None -> Error (MissingTransition at)
    | Some t ->
      Ok
        { net with
          transitions =
            Transitions.add
              at
              { t with coloring = Coloring.add color t.coloring }
              net.transitions
        }
  ;;

  (** Adds a probe on output tokens of the transition. *)
  let add_probe id m at net =
    match Probes.find_opt id net.probes with
    | None -> Ok { net with probes = Probes.add id (m, at) net.probes }
    | Some (existing_m, existing_at) ->
      if compare_color_match existing_m m = 0 && Transition.compare existing_at at = 0
      then Ok net
      else Error (IncompatibleProbeDefinition id)
  ;;

  module Compiled = struct
    type ctransition =
      { inputs : inner_place ref list
      ; outputs : inner_place ref list
      ; coloring : Coloring.t
      ; extracts : (color_match * token Dynarray.t) list
      }

    type t =
      { event_index : ctransition list Events.t
      ; extracted : token Dynarray.t Probes.t
      }

    let of_dynamic { places; transitions; probes } : t =
      let ref_places = Places.map ref places in
      let ref_tokens_probes = Probes.map (fun _ -> Dynarray.create ()) probes in
      let transition_to_probe =
        Probes.fold
          (fun id (m, t) index ->
             Transitions.entry
               ~default:[]
               (List.cons (m, Probes.find id ref_tokens_probes))
               t
               index)
          probes
          Transitions.empty
      in
      let place_list place_ids =
        let unique_place_ids = List.sort_uniq Place.compare place_ids in
        List.map (fun place -> Places.find place ref_places) unique_place_ids
      in
      let fold_transition id { input_arcs; output_arcs; event; coloring } index =
        let inputs = place_list input_arcs in
        let outputs = place_list output_arcs in
        let extracts =
          Option.value ~default:[] @@ Transitions.find_opt id transition_to_probe
        in
        let transition = { inputs; outputs; coloring; extracts } in
        Events.entry ~default:[] (List.cons transition) event index
      in
      let event_index = Transitions.fold fold_transition transitions Events.empty in
      { event_index; extracted = ref_tokens_probes }
    ;;

    let consume_seq_trace ~to_iter:to_seq network trace : t =
      let process_event time net event =
        let transitions = Events.find event net.event_index in
        List.iter
          (fun { inputs; outputs; coloring; extracts } ->
             let can_read input_place =
               let token, _ = read_from_place !input_place in
               Option.is_some token
             in
             let can_read_all = List.for_all can_read inputs in
             if can_read_all
             then (
               let read_token input_place =
                 let token, new_place = read_from_place !input_place in
                 input_place := new_place;
                 token
               in
               let input_tokens = List.filter_map read_token inputs in
               let combined_input =
                 List.fold_left merge_tokens empty_token input_tokens
               in
               let token = visit combined_input event time coloring in
               let write_token output_place =
                 output_place := write_to_place token !output_place
               in
               List.iter write_token outputs;
               let extract_token (color_match, probe_list) =
                 if check_color_match token.coloring color_match
                 then Dynarray.add_last probe_list token
               in
               List.iter extract_token extracts))
          transitions;
        net
      in
      let process_step net Trace.{ label; time } =
        Seq.fold_left (process_event time) net (to_seq label)
      in
      Seq.fold_left process_step network trace
    ;;

    let extracted network = network.extracted
  end
end

module EventEqTransition (T : sig
    include T
    module Transition = Event

    type transition = Transition.t
  end) =
struct
  include Network (T)

  (** Adds a place under a variable and arcs in transitions reading and writing to the place. *)
  let declare_data_connection construct_place variable_name writes reads net =
    let open Result.Syntax in
    let* net = construct_place variable_name net in
    let populate_transition net event = add_transition event event net in
    let populate_read net event =
      let* net = populate_transition net event in
      add_dependency event variable_name net
    in
    let populate_write net event =
      let* net = populate_transition net event in
      add_cause event variable_name net
    in
    let* net = List.fold_leftr populate_write net writes in
    let* net = List.fold_leftr populate_read net reads in
    Ok net
  ;;

  (** Established an order-dependent one-to-many relation between write and read events. *)
  let sampling_variable = declare_data_connection add_variable

  (** Establishes a one-to-one relationship between the write and read events. *)
  let queueing = declare_data_connection add_queue

  (** Largest difference between the witnessed event timestampts. *)
  let witness_interval token =
    (* FIXME: it is probably a good idea to indicate the start points *)
    let (_, ts_min), (_, ts_max) =
      List.minmax (fun (_, ts1) (_, ts2) -> Time.compare ts1 ts2) token.visits
    in
    Time.sub ts_max ts_min
  ;;

  (** Computes shortest and longest event chains that pass through the same event. *)
  let shortest_longest_chains event tokens =
    let is_event (e, _) = Event.compare event e = 0 in
    let one_event_equality { visits = v1; _ } { visits = v2; _ } =
      (* FIXME: linear search on linked list, will cause problems with long chains. *)
      let witness1 = List.find_opt is_event v1
      and witness2 = List.find_opt is_event v2 in
      match witness1, witness2 with
      | Some (_, ts1), Some (_, ts2) -> Time.compare ts1 ts2 = 0
      | _ -> false
    in
    let continuous_groups = Seq.group one_event_equality (Dynarray.to_seq tokens) in
    Seq.filter_map
      (fun group ->
         let with_spans = Seq.map (fun token -> token, witness_interval token) group in
         Seq.minmax
           (fun (_, interval1) (_, interval2) -> Time.compare interval1 interval2)
           with_spans)
      continuous_groups
  ;;

  (** Adds full interval causal link. Corresponds to the time between the event and its previous appearence with a successful chain.*)
  let full_interval event chains =
    let get_event_timestamp (token, _) =
      let* _, timestamp =
        List.find_opt (fun (e, _) -> Event.compare event e = 0) token.visits
      in
      Some timestamp
    in
    let rec aux prev seq () =
      match seq () with
      | Seq.Nil -> Seq.Nil
      | Seq.Cons (chain, rest) ->
        (match get_event_timestamp chain with
         | None -> Seq.Nil
         | Some next -> Cons ((chain, Time.sub next prev), aux next rest))
    in
    let prev, seq = Seq.uncons_opt chains in
    match Option.bind prev get_event_timestamp with
    | None -> Seq.empty
    | Some prev -> aux prev seq
  ;;

  (** Adds reduced interval causal link. Corresponds to the time between the event and its previous appearence. *)
  let reduced_interval ~to_seq event chains trace =
    let is_event e = Event.compare event e = 0 in
    let trace =
      Seq.flat_map
        (fun Trace.{ label; time } -> Seq.map (fun e -> e, time) (to_seq label))
        trace
    in
    let rec advance_until next_event_time previous_seeing trace =
      match trace () with
      | Seq.Cons ((e, time), xs) ->
        if Time.compare time next_event_time = 0
        then previous_seeing, Seq.cons (e, time) xs
        else (
          let previous_seeing =
            if Event.compare e event = 0 then Some time else previous_seeing
          in
          advance_until next_event_time previous_seeing xs)
      | Seq.Nil ->
        failwith
          "CauseEffect.reduced_interval: impossible situation, trace finished before \
           chain"
    in
    let rec aux chains trace () =
      match chains () with
      | Seq.Nil -> Seq.Nil
      | Seq.Cons (chain, rest) ->
        let _, time = List.find (fun (e, _) -> is_event e) chain.visits in
        let previous, trace = advance_until time None trace in
        (match previous with
         | None -> aux rest trace ()
         | Some previous -> Seq.Cons ((chain, Time.sub time previous), aux rest trace))
    in
    aux chains trace
  ;;
end

let%test_module "causal witness flow network" =
  (module struct
    include EventEqTransition (struct
        module Event = String
        module Transition = String
        module Place = String
        module Probe = Integer
        module Color = String
        module Time = Integer

        type place = Place.t
        type event = Event.t
        type probe = Probe.t
        type time = Time.t
        type color = Color.t
        type transition = Transition.t
      end)

    let s = "sensor"
    let c = "controller"
    let a = "actuator"
    let q = "queue"
    let v = "variable"
    let chain_color = "test"
    let chain_probe = 0

    (** s -> c ? a
     s period = 3
     c event-triggered on s
     a period = 5 *)
    let net =
      Result.get_ok
        Result.Syntax.(
          let net = empty in
          let* net = queueing q [ s ] [ c ] net in
          let* net = sampling_variable v [ c ] [ a ] net in
          let* net = inject_color s chain_color net in
          let* net = add_probe chain_probe (Single chain_color) a net in
          Ok net)
    ;;

    let trace1 =
      Trace.
        [ { label = [ s; c; a ]; time = 0 }
        ; { label = []; time = 1 }
        ; { label = []; time = 2 }
        ; { label = [ s; c ]; time = 3 }
        ; { label = []; time = 4 }
        ; { label = [ a ]; time = 5 }
        ; { label = [ s; c ]; time = 6 }
        ]
    ;;

    let trace2 = Trace.[ { label = [ s; a; c ]; time = 0 } ]

    open Ppx_sexp_conv_lib.Conv
    open Ppx_compare_lib.Builtin

    let get_chains trace =
      let compiled_net = Compiled.of_dynamic net in
      let compiled_net =
        Compiled.consume_seq_trace ~to_iter:List.to_seq compiled_net (List.to_seq trace)
      in
      let probes = Compiled.extracted compiled_net in
      let chains = Probes.find chain_probe probes in
      Dynarray.to_list chains
    ;;

    let%test_unit "nominal" =
      [%test_eq: token list]
        (get_chains trace1)
        [ { visits = [ a, 0; c, 0; s, 0 ]; coloring = Coloring.singleton chain_color }
        ; { visits = [ a, 5; c, 3; s, 3 ]; coloring = Coloring.singleton chain_color }
        ]
    ;;

    let%test_unit "unfavorable microstep" = [%test_eq: token list] (get_chains trace2) []
  end)
;;
