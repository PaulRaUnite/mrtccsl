open Common
open Prelude

(** Semantics of ends of causal-effect chains. *)
type end_semantics =
  | Early (** Early denotes early cause or effect among equivalent. *)
  | Late (** Late denotes late cause or effect among equivalent. *)

module Make (Impl : Impl.S) (IDs : Signature.IDs) (Time : Signature.Time) = struct
  include Impl (IDs) (Time)

  module C = struct
    let first ~eq =
      let first = ref None in
      fun x ->
        match !first with
        | Some state ->
          if eq state x
          then None
          else (
            first := Some x;
            Some x)
        | None ->
          first := Some x;
          Some x
    ;;

    let last ~eq =
      let last = ref None in
      fun x ->
        match !last with
        | Some state ->
          last := Some x;
          if eq state x then None else Some state
        | None ->
          last := Some x;
          None
    ;;

    let fanout fs x = Iarray.iter (fun f -> f x) fs

    let buffer_one () =
      let prev = ref None in
      fun x ->
        match !prev with
        | Some y ->
          prev := Some x;
          Some (y, x)
        | None ->
          prev := Some x;
          None
    ;;

    let sink_to_dynarr () =
      let arr = Dynarray.create () in
      arr, Dynarray.add_last arr
    ;;
  end

  (** Filters and maps tokens by selecting chain between the pair of cause and effect (reaction) in the equivalence class and the token. *)
  let select_relevant_tokens ~cause ~conseq color =
    let dep_select =
      match cause with
      | Early -> Token.early_cause_select
      | Late -> Token.late_cause_select
    in
    let eq = Token.has_common_instants in
    let select_conseq =
      (* here we rely on the order of token appearence: it should be monotonic to the passage of time *)
      match conseq with
      | Early -> C.first ~eq
      | Late -> C.last ~eq
    in
    let opt token =
      if Token.contains_internal token
      then None
      else
        let* narrowed = Token.chromatic_filter color token in
        let canonical_cause = Token.subcause ~dep_select narrowed in
        let* canonical_cause_conseq = select_conseq canonical_cause in
        Some canonical_cause_conseq
    in
    opt
  ;;

  (** When computing intervals between chains, each chain should have selected exactly one cause. *)
  exception IntervalMultipleCauses

  (** Returns unique cause mark. @raises IntervalMultipleCauses when tokens were not pre-filtered to contain singular cause. *)
  let cause_mark token =
    let original_causes = Token.non_transitive_causes token in
    let next_ref_instant =
      (* we require the cause to be only one *)
      match original_causes with
      | [ single ] -> single
      | _ -> raise IntervalMultipleCauses
    in
    next_ref_instant
  ;;

  let only_reaction ~cause ~conseq color sink =
    let select_relevant = select_relevant_tokens ~cause ~conseq color in
    let reaction token =
      let* relevant = select_relevant token in
      let start = cause_mark relevant
      and finish = Token.root_mark relevant in
      let _, time1 = Token.mark_instant start
      and _, time2 = Token.mark_instant finish in
      let reaction = Time.sub time2 time1 in
      Some ([ "reaction", Time.one ], reaction)
    in
    fun token -> Option.iter sink (reaction token)
  ;;

  (** Adds duration of the interval between (succesuful) causal-effect chains (tokens).  *)
  let full_interval ~cause ~conseq color sink =
    let select_relevant = select_relevant_tokens ~cause ~conseq color in
    let buffer = C.buffer_one () in
    let reaction token =
      let* relevant = select_relevant token in
      let* x, y = buffer relevant in
      let x = cause_mark x in
      let start = cause_mark y
      and finish = Token.root_mark y in
      let _, time0 = Token.mark_instant x
      and _, time1 = Token.mark_instant start
      and _, time2 = Token.mark_instant finish in
      let interval = Time.sub time1 time0
      and reaction = Time.sub time2 time1
      and total = Time.sub time2 time0 in
      Some
        ( [ "interval", Time.div interval total; "reaction", Time.div reaction total ]
        , total )
    in
    fun token -> Option.iter sink (reaction token)
  ;;

  module TimeSet = Set.Make (Time)

  let reduced_interval ~cause ~conseq color sink =
    let select_relevant = select_relevant_tokens ~cause ~conseq color in
    let times_so_far = ref TimeSet.empty in
    let causes time = times_so_far := TimeSet.add time !times_so_far
    and chain token =
        let token_marks = Token.non_transitive_causes token in
        let* relevant_token = select_relevant token in
        let token_times = List.map (Token.mark_instant >> snd) token_marks in
        let token_times = TimeSet.of_list token_times in
        let earliest_cause_time = TimeSet.min_elt token_times in
        let prev_times =
          TimeSet.filter
            (fun x -> Time.compare x earliest_cause_time < 0)
            !times_so_far
        in
        let* last_time = TimeSet.max_elt_opt prev_times in
        let start = cause_mark relevant_token
        and finish = Token.root_mark relevant_token in
        let time0 = last_time
        and _, time1 = Token.mark_instant start
        and _, time2 = Token.mark_instant finish in
        let interval = Time.sub time1 time0
        and reaction = Time.sub time2 time1
        and total = Time.sub time2 time0 in
        times_so_far := token_times;
        Some
          ( [ "interval", Time.div interval total; "reaction", Time.div reaction total ]
          , total )
    in
    let consume_chain token = Option.iter sink (chain token) in
    causes, consume_chain
  ;;

  type interval_variants =
    { without : (string, Time.t) Stats.record Dynarray.t
    ; full : (string, Time.t) Stats.record Dynarray.t
    ; reduced : (string, Time.t) Stats.record Dynarray.t
    }

  module ProbeMap = Map.Make (IDs.Probe)

  let collect ~cause ~conseq decl trace =
    let net = of_decl decl in
    let result, start, finish =
      List.fold_left
        (fun (store, start, finish) -> function
           | Declaration.Probe { name; at = _; color } ->
             let without, ws = C.sink_to_dynarr ()
             and full, fs = C.sink_to_dynarr ()
             and reduced, rs = C.sink_to_dynarr () in
             let record = { without; full; reduced } in
             let reaction_driver = only_reaction ~cause ~conseq color ws
             and full_interval_driver = full_interval ~cause ~conseq color fs
             and start_driver, reduced_interval_driver =
               reduced_interval ~cause ~conseq color rs
             in
             let finish_driver =
               C.fanout
                 [| reaction_driver; full_interval_driver; reduced_interval_driver |]
             in
             ( ProbeMap.add name record store
             , ProbeMap.add name start_driver start
             , ProbeMap.add name finish_driver finish )
           | _ -> store, start, finish)
        (ProbeMap.empty, ProbeMap.empty, ProbeMap.empty)
        decl
    in
    let start probe = ProbeMap.find probe start
    and finish probe = ProbeMap.find probe finish in
    consume_trace net ~start ~finish trace;
    result
  ;;

  let seq_list_without list =
    list |> List.to_seq |> Seq.flat_map (fun { without; _ } -> Dynarray.to_seq without)
  ;;

  let seq_list_full list =
    list |> List.to_seq |> Seq.flat_map (fun { full; _ } -> Dynarray.to_seq full)
  ;;

  let seq_list_reduced list =
    list |> List.to_seq |> Seq.flat_map (fun { reduced; _ } -> Dynarray.to_seq reduced)
  ;;
end
