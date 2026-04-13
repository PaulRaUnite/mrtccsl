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
    | Variable (token, init) -> if init then Some token, p else Some Token.internal, p
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
      { inputs : place ref iarray
      ; outputs : place ref iarray
      ; coloring : Token.Coloring.t
      ; extracts : (Color.t * Probe.t) iarray
      ; eventually_causes : Probe.t iarray
      }

    type t = { event_index : ctransition iarray Events.t }

    module ColorMap = Map.Make (Color)

    (** Compiles the network. *)
    let of_network { places; transitions; probes } : t =
      let colors_to_probes =
        Probes.fold
          (fun id (color, _) acc -> ColorMap.entry ~default:[] (List.cons id) color acc)
          probes
          ColorMap.empty
      in
      let ref_places = Places.map ref places in
      let transition_to_probe =
        Probes.fold
          (fun id (color, t) index ->
             Transitions.entry ~default:[] (List.cons (color, id)) t index)
          probes
          Transitions.empty
      in
      let place_iarray place_ids =
        let unique_place_ids = List.sort_uniq Place.compare place_ids in
        let place_list =
          List.map (fun place -> Places.find place ref_places) unique_place_ids
        in
        Iarray.of_list place_list
      in
      let fold_transition id { input_arcs; output_arcs; event; coloring } index =
        let inputs = place_iarray input_arcs in
        let outputs = place_iarray output_arcs in
        let extracts =
          Option.value ~default:[] @@ Transitions.find_opt id transition_to_probe
        in
        let extracts = Iarray.of_list extracts in
        let eventually_causes =
          Token.Coloring.fold
            (fun color acc ->
               let potential_probes = ColorMap.value ~default:[] color colors_to_probes in
               List.append potential_probes acc)
            coloring
            []
        in
        let eventually_causes = Iarray.of_list eventually_causes in
        let transition = { inputs; outputs; coloring; extracts; eventually_causes } in
        Events.entry ~default:[] (List.cons transition) event index
      in
      let event_index = Transitions.fold fold_transition transitions Events.empty in
      let event_index = Events.map Iarray.of_list event_index in
      { event_index }
    ;;

    (** Raised when all transitions related to the event cannot be performed. *)
    exception InstantNotConsumed of (Event.t * Time.t)
    [@@deriving sexp]

    (** Consumes sequence of steps in a trace and collects cause witnesses at probe transitions. *)
    let consume_trace network ~start ~finish (trace : _ Trace.t) : unit =
      let try_transition
            instant
            { inputs; outputs; coloring; extracts; eventually_causes }
        =
        let can_read input_place =
          let token, _ = read_from_place !input_place in
          Option.is_some token
        in
        let can_read_all = Iarray.for_all can_read inputs in
        (* Transition is only enabled and fired if all inputs have tokens. *)
        if can_read_all
        then (
          let read_token input_place =
            let token, new_place = read_from_place !input_place in
            input_place := new_place;
            Option.unwrap ~expect:"place is not empty" token
          in
          let input_tokens = Iarray.map read_token inputs in
          let token : Token.t =
            Token.build_external instant coloring (Iarray.to_list input_tokens)
          in
          let write_token output_place =
            output_place := write_to_place token !output_place
          in
          Iarray.iter write_token outputs;
          let extract_token (color_match, probe_id) =
            if Token.Coloring.mem color_match (Token.colors token)
            then finish probe_id token
          in
          Iarray.iter extract_token extracts;
          let extract_potential_cause probe = start probe (snd instant) in
          Iarray.iter extract_potential_cause eventually_causes;
          true)
        else false
      in
      let process_step net Trace.{ label; time } =
        let transitions = Events.find_opt label net.event_index in
        match transitions with
        | Some transitions ->
          let instant = label, time in
          if Iarray.exists (try_transition instant) transitions
          then net
          else raise (InstantNotConsumed instant)
        | None -> net
      in
      ignore @@ Seq.fold_left process_step network trace
    ;;
  end
end

module EventEqTransition (IDs : Impl.I) (Time : Signature.Time) = struct
  module Net =
    Network
      (struct
        include IDs
        module Color = Chain
        module Probe = Chain
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
      | Chain { name; alternatives } ->
        let net =
          List.fold_left
            (fun net chain ->
               assert (List.length chain >= 2);
               let first = Option.unwrap ~expect:"" @@ List.first chain
               and last = Option.unwrap ~expect:"" @@ List.last chain in
               let net = Net.inject_color first name net in
               let net = Net.add_probe name name last net in
               net)
            net
            alternatives
        in
        prev_places, net
    in
    let _, net = List.fold_left execute_record (Places.empty, Net.empty) records in
    of_network net
  ;;
end

let%test_module "causal witness flow network" = (module Test.Make (EventEqTransition))
