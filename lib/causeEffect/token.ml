open Common
open Prelude
open Ppx_sexp_conv_lib.Conv
open Ppx_compare_lib.Builtin

module type IDs = sig
  module Color : Signature.ID
  module Event : Signature.ID
end

module type Time = sig
  include Signature.ID

  val min : t -> t -> t
  val max : t -> t -> t
end

(** Type of causality annotations. *)
type ('time, 'coloring) annot =
  { colors : 'coloring (** Remembers all colors at this point. *)
  ; external_span : ('time * 'time) option
    (** Time interval of all purely external (read: non-transitive) instants. Basically build index in a tree. *)
  }
[@@deriving sexp, compare]

type ('event, 'time) instant = 'event * 'time [@@deriving sexp, compare]

type ('event, 'time, 'coloring) mark =
  { instant : ('event, 'time) instant
  ; annotation : ('time, 'coloring) annot
  }
[@@deriving sexp, compare]

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

type ('event, 'time, 'coloring) t = ('event, 'time, 'coloring) mark cause
[@@deriving sexp, compare]

module type S = sig
  type event
  type time
  type color

  module InstantSet : Set.S with type elt = (event, time) instant
  module Coloring : Set.S with type elt = color

  type nonrec instant = (event, time) instant
  type nonrec annot = (time, Coloring.t) annot
  type nonrec mark = (event, time, Coloring.t) mark
  type nonrec t = (event, time, Coloring.t) t

  val t_of_sexp : Sexplib0.Sexp.t -> t
  val sexp_of_t : t -> Sexplib0.Sexp.t
  val compare : t -> t -> int
  val root_mark_opt : 'a cause -> 'a option
  val mark_instant : mark -> event * time
  val mark_annot : mark -> annot
  val annot_colors : annot -> Coloring.t
  val annot_span : annot -> (time * time) option

  exception NoRootMark

  val root_mark : 'a cause -> 'a
  val non_transitive_causes : 'a cause -> 'a list
  val colors : mark cause -> Coloring.t
  val internal : 'a cause
  val dependencies_annotation : mark cause list -> annot
  val build_external : instant -> Coloring.t -> mark cause list -> mark cause
  val contains_internal : 'a cause -> bool
  val is_internal_free : 'a cause -> bool
  val chromatic_filter : color -> mark cause -> mark cause option
  val unique_instants : mark cause -> InstantSet.t
  val has_common_instants : mark cause -> mark cause -> bool

  val earliest_latest_conseq
    :  minmax:((mark cause -> mark cause -> int) -> 'e -> 'f)
    -> 'e
    -> 'f

  val subcause
    :  dep_select:('a option * 'b cause list -> 'b cause -> 'a option * 'b cause list)
    -> 'b cause
    -> 'b cause

  val early_cause_select
    :  time option * mark cause list
    -> mark cause
    -> time option * mark cause list

  val late_cause_select
    :  time option * mark cause list
    -> mark cause
    -> time option * mark cause list
end

module Make (Event : Signature.ID) (Time : Time) (Color : Signature.ID) = struct
  (** Module of tokens. *)

  type event = Event.t
  type time = Time.t
  type color = Color.t

  module Coloring = struct
    module Inner = Set.Make (Color)
    include Inner
    include Interface.Concrete.Make.SexpForMonoid (Inner) (Color)
  end

  module Instant = struct
    (** Type of instants. *)
    type t = (Event.t, Time.t) instant [@@deriving compare, sexp]
  end

  module InstantSet = Set.Make (Instant)

  module Annot = struct
    type t = (Time.t, Coloring.t) annot

    (** Merges two annotations by union of colors and intervals. *)
    let merge
          { colors = c1; external_span = span1 }
          { colors = c2; external_span = span2 }
      =
      let colors = Coloring.union c1 c2
      and external_span =
        match span1, span2 with
        | Some (min1, max1), Some (min2, max2) ->
          Some (Time.min min1 min2, Time.max max1 max2)
        | None, Some (x, y) | Some (x, y), None -> Some (x, y)
        | None, None -> None
      in
      { colors; external_span }
    ;;

    let empty = { colors = Coloring.empty; external_span = None }
  end

  type nonrec instant = (Event.t, Time.t) instant
  type nonrec annot = (Time.t, Coloring.t) annot
  type nonrec mark = (Event.t, Time.t, Coloring.t) mark

  let mark_instant { instant; _ } = instant
  let mark_annot { annotation; _ } = annotation
  let annot_colors { colors; _ } = colors
  let annot_span { external_span; _ } = external_span

  (** Token type. Represents data passing mark a system. Witnesses the relationships between events from the data interactions. Has an arbitrary combined categorization (color). *)
  type nonrec t = (Event.t, Time.t, Coloring.t) t

  let t_of_sexp = t_of_sexp Event.t_of_sexp Time.t_of_sexp Coloring.t_of_sexp
  let sexp_of_t = sexp_of_t Event.sexp_of_t Time.sexp_of_t Coloring.sexp_of_t
  let compare = compare Event.compare Time.compare Coloring.compare

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
    let annotations =
      List.filter_map
        (fun t ->
           let* mark = root_mark_opt t in
           Some (mark_annot mark))
        dependencies
    in
    let annot = List.fold_left Annot.merge Annot.empty annotations in
    annot
  ;;

  (** Builds an external token, instants without dependencies are considered primary instants. *)
  let build_external instant new_colors dependencies =
    let annotation =
      if List.is_empty dependencies
      then (
        let _, time = instant in
        let external_span = Some (time, time) in
        { colors = new_colors; external_span })
      else (
        let { colors; external_span } = dependencies_annotation dependencies in
        let colors = Coloring.union new_colors colors in
        { colors; external_span })
    in
    let mark = { instant; annotation } in
    External { mark; dependencies }
  ;;

  (** Check whenever the token depends on interval data. *)
  let rec contains_internal = function
    | Internal -> true
    | External { dependencies; _ } -> List.exists contains_internal dependencies
  ;;

  (** Returns true when there are no internal tokens. *)
  let is_internal_free cause = not (contains_internal cause)

  (** Filters out the causality branches that do not contain the specified color scheme. Rebuilds the span index. *)
  let rec chromatic_filter color = function
    | Internal -> None
    | External { dependencies; mark } ->
      let { colors; _ } = mark.annotation in
      if Coloring.mem color colors
      then (
        let filtered_dependencies =
          List.filter_map (chromatic_filter color) dependencies
        in
        let { instant; annotation = { colors; _ } } = mark in
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
    | Some { annotation = { external_span = Some (current_min, _); _ }; _ } ->
      (match state with
       | Some min ->
         let comparison = Time.compare min current_min in
         if comparison = 0
         then state, cause :: result
         else if comparison < 0
         then state, result
         else Some current_min, [ cause ]
       | None -> Some current_min, [ cause ])
    | _ -> state, result
  ;;

  (** Selects dependencies of a cause that contain {b latest} external instant. *)
  let late_cause_select (state, result) cause =
    let node = root_mark_opt cause in
    match node with
    | Some { annotation = { external_span = Some (_, current_max); _ }; _ } ->
      (match state with
       | Some max ->
         let comparison = Time.compare max current_max in
         if comparison = 0
         then state, cause :: result
         else if comparison < 0
         then Some current_max, [ cause ]
         else state, result
       | None -> Some current_max, [ cause ])
    | _ -> state, result
  ;;
end
