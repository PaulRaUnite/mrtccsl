open Common
open Prelude
open Ppx_sexp_conv_lib.Conv

(** Functor that provides construction and traversal of causal (mark data sharing) networks. *)
module Network (IDs : Signature.ExtIDs) (Time : Signature.Time) = struct
  module Time = struct
    include Time
    include Interface.ExpOrder.Make (Time)
  end

  include IDs
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
  module Token = Token.Make (Event) (Time) (Color)

  (** Variable type. *)
  type place =
    | Variable of Token.t * bool
    | Queue of Token.t list
  (* | Buffer of
        { max : int
        ; data : Token.t list
        }
    | SlidingWindow of
        { len : int
        ; data : Token.t list
        } *)

  (** Read semantics of places. *)
  let read_from_place p =
    match p with
    | Variable (token, init) -> if init then Some token, p else None, p
    | Queue q ->
      let hd, tail = List.first_partition q in
      hd, Queue tail
  ;;

  (** Write semantics of places. *)
  let write_to_place token = function
    | Variable (_, _) -> Variable (token, true)
    | Queue q -> Queue (List.append q [ token ])
  ;;

  type transition =
    { input_arcs : Place.t list
    ; output_arcs : Place.t list
    ; coloring : Token.Coloring.t
    ; event : Event.t
    }

  (** Network type. *)
  type t =
    { places : place Places.t
    ; transitions : transition Transitions.t
    ; probes : (Color.t * Transition.t) Probes.t
    }

  (** Empty network. *)
  let empty =
    { places = Places.empty; transitions = Transitions.empty; probes = Probes.empty }
  ;;

  (** Raised when code declares that a place is both variable and queue at the same time. *)
  exception IncompatiblePlaceDefinition of Place.t
  [@@deriving sexp]

  (** Raised when transition is expected, but not found. *)
  exception MissingTransition of Transition.t
  [@@deriving sexp]

  (** Raised when transition is declared twice with different events. *)
  exception IncompatibleTransitionDefinition of Transition.t
  [@@deriving sexp]

  (** Raised when probe is declared twice with different matching colors or at different transition. *)
  exception IncompatibleProbeDefinition of Probe.t
  [@@deriving sexp]

  (** Adds variable place to the network. *)
  let add_variable id net =
    match Places.find_opt id net.places with
    | Some (Variable _) -> net
    | Some _ -> raise (IncompatiblePlaceDefinition id)
    | None ->
      { net with places = Places.add id (Variable (Token.internal, false)) net.places }
  ;;

  (** Adds queue variable to the network. *)
  let add_queue id net =
    match Places.find_opt id net.places with
    | Some (Queue _) -> net
    | Some _ -> raise (IncompatiblePlaceDefinition id)
    | None -> { net with places = Places.add id (Queue []) net.places }
  ;;

  (** Adds an empty transition with an event. *)
  let add_transition id event net =
    match Transitions.find_opt id net.transitions with
    | None ->
      let empty_transition =
        { input_arcs = []; output_arcs = []; event; coloring = Token.Coloring.empty }
      in
      { net with transitions = Transitions.add id empty_transition net.transitions }
    | Some t ->
      if Event.compare t.event event = 0
      then net
      else raise (IncompatibleTransitionDefinition id)
  ;;

  let modify_transition id f net =
    match Transitions.find_opt id net.transitions with
    | None -> raise (MissingTransition id)
    | Some t -> { net with transitions = Transitions.add id (f t) net.transitions }
  ;;

  (** Adds input arc (dependency) to a transition. All inputs need to have data in order to activate the transition. *)
  let add_source id source net =
    modify_transition id (fun t -> { t with input_arcs = source :: t.input_arcs }) net
  ;;

  (** Adds output arc (cause) to a transition. *)
  let add_target id target net =
    modify_transition id (fun t -> { t with output_arcs = target :: t.output_arcs }) net
  ;;

  (** Adds coloring to output tokens of a transition. *)
  let inject_color at color net =
    modify_transition
      at
      (fun t -> { t with coloring = Token.Coloring.add color t.coloring })
      net
  ;;

  (** Adds a probe on output tokens of the transition. *)
  let add_probe id m at net =
    match Probes.find_opt id net.probes with
    | None -> { net with probes = Probes.add id (m, at) net.probes }
    | Some (existing_m, existing_at) ->
      if Color.compare existing_m m = 0 && Transition.compare existing_at at = 0
      then net
      else raise (IncompatibleProbeDefinition id)
  ;;

  (** Module for networks ready to travers traces efficiently. The representation is mutable. *)
  module Compiled = struct
    type ctransition =
      { inputs : place ref list
      ; outputs : place ref list
      ; coloring : Token.Coloring.t
      ; extracts : (Color.t * Token.t Dynarray.t) list
      }

    type t =
      { event_index : ctransition list Events.t
      ; extracted : (Color.t * Token.t Dynarray.t) Probes.t
      }

    (** Compiles the network. *)
    let of_network { places; transitions; probes } : t =
      let ref_places = Places.map ref places in
      let ref_tokens_probes = Probes.map (fun (m, _) -> m, Dynarray.create ()) probes in
      let transition_to_probe =
        Probes.fold
          (fun id (_, t) index ->
             Transitions.entry
               ~default:[]
               (List.cons (Probes.find id ref_tokens_probes))
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

    (** Consumes sequence of steps in a trace and collects cause witnesses at probe transitions. *)
    let consume_seq_trace network trace : t =
      let try_transition instant { inputs; outputs; coloring; extracts } =
        let can_read input_place =
          let token, _ = read_from_place !input_place in
          Option.is_some token
        in
        let can_read_all = List.for_all can_read inputs in
        (* Transition is only enabled and fired if all inputs have tokens. *)
        if can_read_all
        then (
          let read_token input_place =
            let token, new_place = read_from_place !input_place in
            input_place := new_place;
            token
          in
          let input_tokens = List.filter_map read_token inputs in
          let token = Token.build_external instant coloring input_tokens in
          let write_token output_place =
            output_place := write_to_place token !output_place
          in
          List.iter write_token outputs;
          let extract_token (color_match, probe_list) =
            if Token.Coloring.mem color_match (Token.colors token)
            then Dynarray.add_last probe_list token
          in
          List.iter extract_token extracts)
      in
      let process_step net Trace.{ label; time } =
        let transitions = Events.find label net.event_index in
        let instant = label, time in
        List.iter (try_transition instant) transitions;
        net
      in
      Seq.fold_left process_step network trace
    ;;

    (** Returns extracted by probes cause witnesses. *)
    let extracted network = network.extracted
  end
end

module EventEqTransition (IDs : Signature.IDs) (Time : Signature.Time) = struct
  module Net =
    Network
      (struct
        include IDs
        module Transition = Event
      end)
      (Time)

  include Net.Compiled
  module Token = Net.Token
  module Places = Net.Places
  module Probes = Net.Probes

  (** Adds a place under a variable and arcs in transitions reading and writing to the place. *)
  let declare_data_connection construct_place variable_name writes reads net =
    let net = construct_place variable_name net in
    let populate_transition net event = Net.add_transition event event net in
    let populate_read net event =
      let net = populate_transition net event in
      Net.add_source event variable_name net
    in
    let populate_write net event =
      let net = populate_transition net event in
      Net.add_target event variable_name net
    in
    let net = List.fold_left populate_write net writes in
    let net = List.fold_left populate_read net reads in
    net
  ;;

  (** Established an order-dependent one-to-many relation between write and read events. *)
  let sampling_variable = declare_data_connection Net.add_variable

  (** Establishes a one-to-one relationship between the write and read events. *)
  let queueing = declare_data_connection Net.add_queue

  (** Cannot have several declarations of the same place. *)
  exception DuplicatePlaceStatements
  [@@deriving sexp]

  (** Converts declaration into a network. *)
  let of_decl records =
    let open Declaration in
    let execute_record (prev_places, net) decl =
      let check_duplicate_place name =
        if Option.is_some @@ Places.find_opt name prev_places
        then raise DuplicatePlaceStatements
      in
      match decl with
      | Variable { name; writes; reads } ->
        check_duplicate_place name;
        let net = sampling_variable name writes reads net
        and places = Places.add name () prev_places in
        places, net
      | Queue { name; writes; reads } ->
        check_duplicate_place name;
        let net = queueing name writes reads net
        and places = Places.add name () prev_places in
        places, net
      | Inject { at; color } -> prev_places, Net.inject_color at color net
      | Probe { name; color; at } -> prev_places, Net.add_probe name color at net
    in
    let _, net = List.fold_left execute_record (Places.empty, Net.empty) records in
    of_network net
  ;;

  let consume_trace net consumers trace =
    let net = consume_seq_trace net trace in
    let probes = extracted net in
    Probes.iter
      (fun probe (_, tokens) ->
         Option.iter (fun consumer -> Dynarray.iter consumer tokens) (consumers probe))
      probes
  ;;

  (** Filters and maps tokens by selecting chain between the pair of cause and effect (reaction) in the equivalence class and the token. *)
  let select_relevant_tokens ~cause ~conseq color_guard tokens =
    let non_internal_tokens = Seq.filter (not << Token.contains_internal) tokens in
    let narrowed_tokens =
      Seq.filter_map (Token.chromatic_filter color_guard) non_internal_tokens
    in
    let equivalence_classes = Seq.group Token.has_common_instants narrowed_tokens in
    let select_canonical_conseq equiv_tokens =
      (*TODO: revise, will probably allow transitive equivalence which is undesirable *)
      let cls = List.of_seq equiv_tokens in
      let equiv_tokens = List.to_seq cls in
      let min, max =
        Option.unwrap ~expect:"group is never empty"
        @@ Token.earliest_latest_conseq ~minmax:Seq.minmax equiv_tokens
      in
      Declaration.(
        match conseq with
        | Early -> min
        | Late -> max)
    in
    let canonical_conseq = Seq.map select_canonical_conseq equivalence_classes in
    let dep_select =
      Declaration.(
        match cause with
        | Early -> Token.early_cause_select
        | Late -> Token.late_cause_select)
    in
    let select_canonical_cause = Token.subcause ~dep_select in
    let canonical_cause_conseq = Seq.map select_canonical_cause canonical_conseq in
    canonical_cause_conseq
  ;;

  (** When computing intervals between chains, each chain should have selected exactly one cause. *)
  exception IntervalMultipleCauses

  (** Adds duration of the interval between (succesuful) causal-effect chains (tokens). @raises IntervalMultipleCauses when tokens were not pre-filtered to contain singular cause. *)
  let full_interval tokens =
    let cause_mark token =
      let original_causes = Token.non_transitive_causes token in
      let next_ref_instant =
        (* we require the cause to be only one *)
        match original_causes with
        | [ single ] -> single
        | _ -> raise IntervalMultipleCauses
      in
      next_ref_instant
    in
    let rec aux prev seq () =
      match seq () with
      | Seq.Nil -> Seq.Nil
      | Seq.Cons (token, rest) ->
        let next_ref = cause_mark token in
        Cons ((prev, token), aux next_ref rest)
    in
    let first, rest = Seq.uncons_opt tokens in
    match Option.map cause_mark first with
    | None -> Seq.empty
    | Some first -> aux first rest
  ;;
  (* TODO: think about implementing reduced interval later
  (** Impossible situation, trace finished before chain. *)
  exception TraceShorterThanChain

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
      | Seq.Nil -> raise TraceShorterThanChain
    in
    let rec aux chains trace () =
      match chains () with
      | Seq.Nil -> Seq.Nil
      | Seq.Cons (chain, rest) ->
        let times =
          Option.unwrap_exn ~expect:(MissingEvent event)
          @@ Events.find_opt event chain.visits
        in
        (* CORRECTNESS: presence of [first] is guaranteed by non-empty option found just above *)
        let first = Dynarray.get times 0 in
        let just_before, trace = advance_until first None trace in
        (match just_before with
         | None -> aux rest trace ()
         | Some previous -> Seq.Cons ((chain, Time.sub first previous), aux rest trace))
    in
    aux chains trace
  ;; *)
end

let%test_module "causal witness flow network" = (module Test.Make (EventEqTransition))
