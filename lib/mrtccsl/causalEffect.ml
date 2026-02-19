open Prelude
open Number

module type P = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
end

module type T = sig
  module Place : P
  module Transition : Interface.TotalOrder
  module Color : P
  module Event : P
  module Probe : P

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
  open Ppx_sexp_conv_lib.Conv
  include T
  module Places = Map.Make (Place)
  module Transitions = Map.Make (Transition)

  module Events = struct
    include Map.Make (Event)

    let sexp_of_t sexp_of_e =
      sexp_of_list (sexp_of_pair Event.sexp_of_t sexp_of_e) << to_list
    ;;

    let t_of_sexp e_of_sexp =
      list_of_sexp (pair_of_sexp Event.t_of_sexp e_of_sexp) >> of_list
    ;;
  end

  module Probes = Map.Make (Probe)

  type place_type =
    | Variable
    | Queue

  module Coloring = struct
    include Set.Make (Color)

    let sexp_of_t = sexp_of_list Color.sexp_of_t << to_list
    let t_of_sexp = list_of_sexp Color.t_of_sexp >> of_list
  end

  type token =
    { visits : Time.t Dynarray.t Events.t
    ; coloring : Coloring.t
    }
  [@@deriving compare, sexp]

  let empty_token = { visits = Events.empty; coloring = Coloring.empty }

  let merge_tokens { visits = v1; coloring = c1 } { visits = v2; coloring = c2 } =
    { visits =
        Events.union
          (fun _ a1 a2 ->
             let arr = Dynarray.append_alloc a1 a2 in
             Dynarray.stable_sort Time.compare arr;
             Some arr)
          v1
          v2
    ; coloring = Coloring.union c1 c2
    }
  ;;

  let visit { visits; coloring } event time more_color =
    let update_array arr =
      Dynarray.add_last arr time;
      arr
    in
    { visits = Events.entry_mut ~default:Dynarray.create update_array event visits
    ; coloring = Coloring.union coloring more_color
    }
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
      let try_transition time event { inputs; outputs; coloring; extracts } =
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
          let combined_input = List.fold_left merge_tokens empty_token input_tokens in
          let token = visit combined_input event time coloring in
          let write_token output_place =
            output_place := write_to_place token !output_place
          in
          List.iter write_token outputs;
          let extract_token (color_match, probe_list) =
            if check_color_match token.coloring color_match
            then Dynarray.add_last probe_list token
          in
          List.iter extract_token extracts)
      in
      let process_event time net event =
        let transitions = Events.find event net.event_index in
        List.iter (try_transition time event) transitions;
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

  module Declaration = struct
    open Sexplib0.Sexp_conv
    open Ppx_compare_lib.Builtin

    type record =
      | Variable of
          { name : T.Place.t
          ; writes : Event.t list
          ; reads : Event.t list
          }
      | Queue of
          { name : T.Place.t
          ; writes : Event.t list
          ; reads : Event.t list
          }
      | Inject of
          { at : Event.t
          ; colors : Color.t list
          }
      | Probe of
          { name : Probe.t
          ; expect_all : Color.t list
          ; at : Event.t
          }
    [@@deriving sexp, compare]

    type t = record list [@@deriving sexp, compare]

    let to_net records =
      let execute_record net = function
        | Variable { name; writes; reads } -> sampling_variable name writes reads net
        | Queue { name; writes; reads } -> queueing name writes reads net
        | Inject { at; colors } ->
          List.fold_leftr (fun net color -> inject_color at color net) net colors
        | Probe { name; expect_all; at } ->
          let individual_matches = List.map (fun c -> Single c) expect_all in
          let all_match = List.fold_merge (fun l r -> And (l, r)) individual_matches in
          add_probe name all_match at net
      in
      List.fold_leftr execute_record empty records
    ;;
  end

  (** Largest difference between the witnessed event timestampts. *)
  let witness_interval token =
    (* FIXME: it is probably a good idea to indicate the start points *)
    let* ts_min, ts_max =
      token.visits
      |> Events.to_seq
      |> Seq.flat_map (fun (_, times) -> Dynarray.to_seq times)
      |> Seq.minmax Time.compare
    in
    Some (Time.sub ts_max ts_min)
  ;;

  (** Computes shortest and longest event chains that pass through the same event. *)
  let shortest_longest_chains event tokens =
    let one_event_equality { visits = v1; _ } { visits = v2; _ } =
      let ts1 = Events.find_opt event v1
      and ts2 = Events.find_opt event v2 in
      match ts1, ts2 with
      | Some ts1, Some ts2 -> Dynarray.compare Time.compare ts1 ts2 = 0
      | _ -> false
    in
    let continuous_groups = Seq.group one_event_equality (Dynarray.to_seq tokens) in
    Seq.filter_map
      (fun group ->
         let with_spans = Seq.map (fun token -> token, witness_interval token) group in
         Seq.minmax
           (fun (_, interval1) (_, interval2) ->
              Option.compare Time.compare interval1 interval2)
           with_spans)
      continuous_groups
  ;;

  exception MissingEvent of Event.t [@@deriving sexp]

  (** Adds full interval causal link. Corresponds to the time between the event and its previous appearence with a successful chain.*)
  let full_interval event chains =
    let get_first_timestamp (token, _) =
      let times =
        Option.unwrap_exn ~expect:(MissingEvent event)
        @@ Events.find_opt event token.visits
      in
      let first = Dynarray.get times 0 in
      first
    in
    let get_last_timestamp (token, _) =
      let times = Events.find event token.visits in
      let first = Dynarray.get_last times in
      first
    in
    let rec aux prev seq () =
      match seq () with
      | Seq.Nil -> Seq.Nil
      | Seq.Cons (chain, rest) ->
        let first = get_first_timestamp chain
        and last = get_last_timestamp chain in
        Cons ((chain, Time.sub first prev), aux last rest)
    in
    let prev, seq = Seq.uncons_opt chains in
    match Option.map get_last_timestamp prev with
    | None -> Seq.empty
    | Some prev -> aux prev seq
  ;;

  (** Adds reduced interval causal link. Corresponds to the time between the event and its previous appearence. *)
  let reduced_interval ~to_seq event chains trace =
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
        let times =
          Option.unwrap_exn ~expect:(MissingEvent event)
          @@ Events.find_opt event chain.visits
        in
        (* CORRECTNESS: presence of [first] should be guaranteed by non-empty option *)
        let first = Dynarray.get times 0 in
        let just_before, trace = advance_until first None trace in
        (match just_before with
         | None -> aux rest trace ()
         | Some previous -> Seq.Cons ((chain, Time.sub first previous), aux rest trace))
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
    let net_description =
      Declaration.
        [ Variable { name = v; writes = [ c ]; reads = [ a ] }
        ; Queue { name = q; writes = [ s ]; reads = [ c ] }
        ; Inject { at = s; colors = [ chain_color ] }
        ; Probe { name = chain_probe; expect_all = [ chain_color ]; at = a }
        ]
    ;;

    let net = Result.get_ok @@ Declaration.to_net net_description

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
      let construct_visits list =
        list |> List.map (fun (e, t) -> e, Dynarray.singleton t) |> Events.of_list
      in
      [%test_eq: token list]
        (get_chains trace1)
        [ { visits = construct_visits [ a, 0; c, 0; s, 0 ]
          ; coloring = Coloring.singleton chain_color
          }
        ; { visits = construct_visits [ a, 5; c, 3; s, 3 ]
          ; coloring = Coloring.singleton chain_color
          }
        ]
    ;;

    let%test_unit "unfavorable microstep" = [%test_eq: token list] (get_chains trace2) []

    let%test_unit "same sexp" =
      [%test_eq: Declaration.t]
        net_description
        (Declaration.t_of_sexp
         @@ Sexplib.Sexp.of_string
              "((Variable  (name variable)(writes(controller))(reads(actuator)))\n\
               (Queue(name queue)(writes(sensor))(reads(controller)))\n\
               (Inject(at sensor)(colors(test)))\n\
               (Probe(name 0)(expect_all(test))(at actuator)))")
    ;;
  end)
;;
