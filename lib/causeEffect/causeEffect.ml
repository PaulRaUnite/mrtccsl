(** Cause-Effect network definitions and traversal. *)

open Common
open Prelude
open Number

module type ID = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
end

module type IDs = sig
  (** Place IDs. *)
  module Place : ID

  (** Transition IDs. *)
  module Transition : ID

  (** Color IDs. *)
  module Color : ID

  (** Event IDs. *)
  module Event : ID

  (** Probe IDs. *)
  module Probe : ID
end

(** Timestamp numbers. *)
module type Time = sig
  include Interface.TotalOrder
  include Sexplib0.Sexpable.S with type t := t
  include Interface.Number.Ring with type t := t
end

(** Functor that provides construction and traversal of causal (mark data sharing) networks. *)
module Network (IDs : IDs) (Time : Time) = struct
  module Time = struct
    include Time
    include Interface.ExpOrder.Make (Time)
  end

  open Ppx_sexp_conv_lib.Conv
  open Ppx_compare_lib.Builtin
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

  module Coloring = struct
    module Inner = Set.Make (Color)
    include Inner
    include Interface.Concrete.Make.SexpForMonoid (Inner) (Color)

    (** Type of color guards. *)
    type guard =
      (* TODO: just reuse propositional formula *)
      | Any
      | Atom of Color.t
      | And of guard list
      | AllAtoms of t
      | Or of guard list
      | AnyAtom of t
    [@@deriving compare]

    let rec eval_guard coloring = function
      | Any -> true
      | AllAtoms colors -> subset coloring colors
      | AnyAtom colors -> not @@ is_empty @@ inter coloring colors
      | Atom color -> mem color coloring
      | And matches -> List.for_all (eval_guard coloring) matches
      | Or matches -> List.exists (eval_guard coloring) matches
    ;;
  end

  module Instant = struct
    (** Type of instants. *)
    type t = Event.t * Time.t [@@deriving compare, sexp]
  end

  module Annot = struct
    (** Type of causality annotations. *)
    type t =
      { colors : Coloring.t (** Remembers all colors at this point. *)
      ; external_span : Time.t * Time.t
        (** Time interval of all purely external (read: non-transitive) instants. Basically build index in a tree. *)
      }
    [@@deriving sexp, compare]

    (** Merges two annotations by union of colors and intervals. *)
    let merge
          { colors = c1; external_span = min1, max1 }
          { colors = c2; external_span = min2, max2 }
      =
      let colors = Coloring.union c1 c2
      and external_span = Time.min min1 min2, Time.max max1 max2 in
      { colors; external_span }
    ;;
  end

  module InstantSet = Set.Make (Instant)

  module Token = struct
    (** Module of tokens. *)

    (** Definition of influence relation for marks of type ['mark]. *)
    type 'mark cause =
      | Internal
      (** Dependency on variable that was initialized to some value at the start of the system. *)
      | External of
          { dependencies : 'mark cause list (** Dependency cannot be empty. *)
          ; mark : 'mark
            (** Event that binds the dependencies into a new relation. Cannot be empty. *)
          } (** Value depends on external activity denoted by the ['mark]. *)
    [@@deriving compare, sexp]

    type mark =
      { instant : Instant.t
      ; annotation : Annot.t
      }
    [@@deriving sexp, compare]

    (** Token type. Represents data passing mark a system. Witnesses the relationships between events from the data interactions. Has an arbitrary combined categorization (color). *)
    type t = mark cause [@@deriving sexp, compare]

    (** Returns [Some] root mark of the token or [None] when token is internal. *)
    let root_mark_opt = function
      | Internal -> None
      | External { mark; _ } -> Some mark
    ;;

    exception NoRootMark

    (** Returns root mark recorded by the token. @raises NoRootMark *)
    let root_mark token = Option.unwrap_exn ~expect:NoRootMark @@ root_mark_opt token

    (** Returns all marks that do not depend on other causes. *)
    let rec non_transitive_causes = function
      | Internal -> []
      | External { mark; dependencies } ->
        if List.is_empty dependencies
        then [ mark ]
        else List.flat_map non_transitive_causes dependencies
    ;;

    (** Token colors. *)
    let colors = function
      | Internal -> Coloring.empty
      | External { mark; _ } -> mark.annotation.colors
    ;;

    (** A default token with internally initialized data and empty coloring. *)
    let internal = Internal

    let dependencies_annotation dependencies =
      let marks =
        List.filter_map
          (fun t ->
             let* mark = root_mark_opt t in
             Some mark.annotation)
          dependencies
      in
      let annot = List.reduce_left Annot.merge Fun.id marks in
      annot
    ;;

    (** Builds an external token, instants without dependencies are considered primary instants. *)
    let build_external instant new_colors dependencies =
      let annotation =
        if List.is_empty dependencies
        then (
          let _, time = instant in
          let external_span = time, time in
          Annot.{ colors = new_colors; external_span })
        else (
          let Annot.{ colors; external_span } = dependencies_annotation dependencies in
          let colors = Coloring.union new_colors colors in
          Annot.{ colors; external_span })
      in
      let mark = { instant; annotation } in
      External { mark; dependencies = dependencies }
    ;;

    (** Check whenever the token depends on interval data. *)
    let rec contains_internal = function
      | Internal -> true
      | External { dependencies; _ } -> List.exists contains_internal dependencies
    ;;

    (** Returns true when there are no internal tokens. *)
    let is_internal_free cause = not (contains_internal cause)

    (** Filters out the causality branches that do not contain the specified color scheme. Rebuilds the span index. *)
    let rec chromatic_filter matching = function
      | Internal -> None
      | External { dependencies; mark } ->
        let Annot.{ colors; _ } = mark.annotation in
        if Coloring.eval_guard colors matching
        then (
          let filtered_dependencies =
            List.filter_map (chromatic_filter matching) dependencies
          in
          let { instant; annotation = Annot.{ colors; _ } } = mark in
          Some (build_external instant colors filtered_dependencies))
        else None
    ;;

    let rec unique_instants instants = function
      | Internal -> instants
      | External { mark = { instant; _ }; dependencies } ->
        let previous_marks =
          List.fold_left
            (fun set influence -> unique_instants set influence)
            instants
            dependencies
        in
        InstantSet.add instant previous_marks
    ;;

    (** Returns all unique instants in a token as a set. *)
    let unique_instants inf = unique_instants InstantSet.empty inf

    (** Checks whenever the tokens share some instants. *)
    let has_common_instants t1 t2 =
      let instants1 = unique_instants t1
      and instants2 = unique_instants t2 in
      not (InstantSet.disjoint instants1 instants2)
    ;;

    (** Returns the earlist and the latest token in the equivalence set sequence. @param minmax is any [minmax] function for [tokens] container. *)
    let earliest_latest_conseq ~minmax tokens =
      minmax
        (fun t1 t2 ->
           let { instant = _, time1; _ } = root_mark t1
           and { instant = _, time2; _ } = root_mark t2 in
           Time.compare time1 time2)
        tokens
    ;;

    (** Narrows causality to the ones that satisfy [~dep_select]. *)
    let rec subcause ~dep_select = function
      | Internal -> Internal
      | External { mark; dependencies } ->
        let _, dependencies = List.fold_left dep_select (None, []) dependencies in
        (* dep_select should select something *)
        let dependencies = List.map (subcause ~dep_select) dependencies in
        External { mark; dependencies }
    ;;

    (** Selects dependencies of a cause that contain {b earliest} external instant. *)
    let early_cause_select (state, result) cause =
      let node = root_mark_opt cause in
      match node with
      | Some node ->
        let Annot.{ external_span = current_min, _; _ } = node.annotation in
        (match state with
         | Some min ->
           let comparison = Time.compare min current_min in
           if comparison = 0
           then state, cause :: result
           else if comparison < 0
           then state, result
           else Some current_min, [ cause ]
         | None -> Some current_min, [ cause ])
      | None -> state, result
    ;;

    (** Selects dependencies of a cause that contain {b latest} external instant. *)
    let late_cause_select (state, result) cause =
      let node = root_mark_opt cause in
      match node with
      | Some node ->
        let Annot.{ external_span = _, current_max; _ } = node.annotation in
        (match state with
         | Some max ->
           let comparison = Time.compare max current_max in
           if comparison = 0
           then state, cause :: result
           else if comparison < 0
           then Some current_max, [ cause ]
           else state, result
         | None -> Some current_max, [ cause ])
      | None -> state, result
    ;;
  end

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
    ; coloring : Coloring.t
    ; event : Event.t
    }

  (** Network type. *)
  type t =
    { places : place Places.t
    ; transitions : transition Transitions.t
    ; probes : (Coloring.guard * Transition.t) Probes.t
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
        { input_arcs = []; output_arcs = []; event; coloring = Coloring.empty }
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
      (fun t -> { t with coloring = Coloring.add color t.coloring })
      net
  ;;

  (** Adds a probe on output tokens of the transition. *)
  let add_probe id m at net =
    match Probes.find_opt id net.probes with
    | None -> { net with probes = Probes.add id (m, at) net.probes }
    | Some (existing_m, existing_at) ->
      if Coloring.compare_guard existing_m m = 0 && Transition.compare existing_at at = 0
      then net
      else raise (IncompatibleProbeDefinition id)
  ;;

  (** Module for networks ready to travers traces efficiently. The representation is mutable. *)
  module Compiled = struct
    type ctransition =
      { inputs : place ref list
      ; outputs : place ref list
      ; coloring : Coloring.t
      ; extracts : (Coloring.guard * Token.t Dynarray.t) list
      }

    type t =
      { event_index : ctransition list Events.t
      ; extracted : (Coloring.guard * Token.t Dynarray.t) Probes.t
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
    let consume_seq_trace ~to_iter:to_seq network trace : t =
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
            if Coloring.eval_guard (Token.colors token) color_match
            then Dynarray.add_last probe_list token
          in
          List.iter extract_token extracts)
      in
      let process_event time net event =
        let transitions = Events.find event net.event_index in
        let instant = event, time in
        List.iter (try_transition instant) transitions;
        net
      in
      let process_step net Trace.{ label; time } =
        Seq.fold_left (process_event time) net (to_seq label)
      in
      Seq.fold_left process_step network trace
    ;;

    (** Returns extracted by probes cause witnesses. *)
    let extracted network = network.extracted
  end
end

module EventEqTransition
    (T : sig
       include IDs
       module Transition = Event
     end)
    (Time : Time) =
struct
  include Network (T) (Time)

  (** Adds a place under a variable and arcs in transitions reading and writing to the place. *)
  let declare_data_connection construct_place variable_name writes reads net =
    let net = construct_place variable_name net in
    let populate_transition net event = add_transition event event net in
    let populate_read net event =
      let net = populate_transition net event in
      add_source event variable_name net
    in
    let populate_write net event =
      let net = populate_transition net event in
      add_target event variable_name net
    in
    let net = List.fold_left populate_write net writes in
    let net = List.fold_left populate_read net reads in
    net
  ;;

  (** Established an order-dependent one-to-many relation between write and read events. *)
  let sampling_variable = declare_data_connection add_variable

  (** Establishes a one-to-one relationship between the write and read events. *)
  let queueing = declare_data_connection add_queue

  module Declaration = struct
    open Sexplib0.Sexp_conv
    open Ppx_compare_lib.Builtin

    (** Declaration statements. *)
    type statement =
      | Variable of
          { name : T.Place.t
          ; writes : Event.t list
          ; reads : Event.t list
          } (** Shared variable declaration. *)
      | Queue of
          { name : T.Place.t
          ; writes : Event.t list
          ; reads : Event.t list
          } (** Queue variable declaration. *)
      | Inject of
          { at : Event.t
          ; colors : Color.t list
          } (** Color injection declaration. *)
      | Probe of
          { name : Probe.t
          ; expect_all : Color.t list
          ; at : Event.t
          } (** Probe declaration. *)
    [@@deriving sexp, compare]

    type t = statement list [@@deriving sexp, compare]

    (** Cannot have several declarations of the same place. *)
    exception DuplicatePlaceStatements
    [@@deriving sexp]

    (** Converts declaration into a network. *)
    let to_network records =
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
        | Inject { at; colors } ->
          ( prev_places
          , List.fold_left (fun net color -> inject_color at color net) net colors )
        | Probe { name; expect_all; at } ->
          let color_guard = Coloring.(AllAtoms (of_list expect_all)) in
          prev_places, add_probe name color_guard at net
      in
      let _, net = List.fold_left execute_record (Places.empty, empty) records in
      net
    ;;
  end

  (** Semantics of ends of causal-effect chains. *)
  type end_semantics =
    | Early (** Early denotes early cause or effect among equivalent. *)
    | Late (** Late denotes late cause or effect among equivalent. *)

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
      match conseq with
      | Early -> min
      | Late -> max
    in
    let canonical_conseq = Seq.map select_canonical_conseq equivalence_classes in
    let dep_select =
      match cause with
      | Early -> Token.early_cause_select
      | Late -> Token.late_cause_select
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

let%test_module "causal witness flow network" =
  (module struct
    include
      EventEqTransition
        (struct
          module Event = String
          module Transition = String
          module Place = String
          module Probe = Integer
          module Color = String
        end)
        (Integer)

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

    let net = Declaration.to_network net_description

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

    let get_tokens trace =
      let compiled_net = Compiled.of_network net in
      let compiled_net =
        Compiled.consume_seq_trace ~to_iter:List.to_seq compiled_net (List.to_seq trace)
      in
      let probes = Compiled.extracted compiled_net in
      let _, tokens = Probes.find chain_probe probes in
      Dynarray.to_list tokens
    ;;

    let%test_unit "nominal" =
      let construct_visits colors list =
        let first instant = Token.build_external instant colors [] in
        let wrap instant cause = Token.build_external instant colors [ cause ] in
        List.reduce_right wrap first list
      in
      let colors = Coloring.singleton chain_color in
      [%test_eq: Token.t list]
        (get_tokens trace1)
        [ construct_visits colors [ a, 0; c, 0; s, 0 ]
        ; construct_visits colors [ a, 5; c, 3; s, 3 ]
        ]
    ;;

    let%test_unit "unfavorable microstep" =
      [%test_eq: Token.t list] (get_tokens trace2) []
    ;;

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
