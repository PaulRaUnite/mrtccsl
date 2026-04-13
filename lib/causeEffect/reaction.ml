open Common
open Prelude

(** Semantics of ends of causal-effect chains. *)
type end_semantics =
  | Early (** Early denotes early cause or effect among equivalent. *)
  | Late (** Late denotes late cause or effect among equivalent. *)

module Make (F : Impl.S) (IDs : Impl.I) (Time : Signature.Time) = struct
  include F (IDs) (Time)

  module C = struct
    let first eq =
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

    let last eq =
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
  let select_relevant_tokens ~cause ~conseq ~path =
    let dep_select =
      match cause with
      | Early -> Token.early_cause_select
      | Late -> Token.late_cause_select
    in
    let eq = Token.has_common_instants in
    let select_conseq =
      (* here we rely on the order of token appearence: it should be monotonic to the passage of time *)
      match conseq with
      | Early -> C.first eq
      | Late -> C.last eq
    in
    let opt token =
      if Token.contains_internal token
      then None
      else
        (* let* narrowed = Token.chromatic_filter color token in *)
        let* token = Token.path_filter path token in
        let canonical_cause = Token.subcause ~dep_select token in
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

  let process_contributions reaction total contributions =
    if Time.compare total Time.zero = 0
    then [ "reaction", Time.zero ]
    else (
      match contributions with
      | Some contributions ->
        List.map
          (fun (prev, next, time0, time1) ->
             let link =
               Printf.sprintf
                 "%s->%s"
                 (IDs.Event.to_string prev)
                 (IDs.Event.to_string next)
             in
             let cont = Time.div (Time.sub time1 time0) total in
             link, cont)
          contributions
      | None -> [ "reaction", Time.div reaction total ])
  ;;

  let only_reaction sink =
    fun (token, contributions) ->
    let start = cause_mark token
    and finish = Token.root_mark token in
    let _, time1 = Token.mark_instant start
    and _, time2 = Token.mark_instant finish in
    let reaction = Time.sub time2 time1 in
    sink (process_contributions reaction reaction contributions, reaction)
  ;;

  (** Adds duration of the interval between (succesuful) causal-effect chains (tokens).  *)
  let full_interval sink =
    let buffer = C.buffer_one () in
    let reaction (token, contributions) =
      let* x, y = buffer token in
      let x = cause_mark x in
      let start = cause_mark y
      and finish = Token.root_mark y in
      let _, time0 = Token.mark_instant x
      and _, time1 = Token.mark_instant start
      and _, time2 = Token.mark_instant finish in
      let interval = Time.sub time1 time0
      and reaction = Time.sub time2 time1
      and total = Time.sub time2 time0 in
      let contributions = process_contributions reaction total contributions in
      Some (("interval", Time.div interval total) :: contributions, total)
    in
    fun token -> Option.iter sink (reaction token)
  ;;

  module TimeSet = Set.Make (Time)

  let reduced_interval sink =
    let times_so_far = ref TimeSet.empty in
    let causes time = times_so_far := TimeSet.add time !times_so_far
    and chain (token, contributions) =
      let token_marks = Token.non_transitive_causes token in
      let token_times = List.map (Token.mark_instant >> snd) token_marks in
      let token_times = TimeSet.of_list token_times in
      let earliest_cause_time = TimeSet.min_elt token_times in
      let prev_times =
        TimeSet.filter (fun x -> Time.compare x earliest_cause_time < 0) !times_so_far
      in
      let* last_time = TimeSet.max_elt_opt prev_times in
      let start = cause_mark token
      and finish = Token.root_mark token in
      let time0 = last_time
      and _, time1 = Token.mark_instant start
      and _, time2 = Token.mark_instant finish in
      let interval = Time.sub time1 time0
      and reaction = Time.sub time2 time1
      and total = Time.sub time2 time0 in
      times_so_far := token_times;
      let contributions = process_contributions reaction total contributions in
      Some (("interval", Time.div interval total) :: contributions, total)
    in
    let consume_chain token = Option.iter sink (chain token) in
    causes, consume_chain
  ;;

  type interval_variants =
    { without : (string, Time.t) Stats.record Dynarray.t
    ; full : (string, Time.t) Stats.record Dynarray.t
    ; reduced : (string, Time.t) Stats.record Dynarray.t
    }

  module ChainMap = Map.Make (IDs.Chain)

  let collect ~cause ~conseq decl trace =
    let net = of_decl decl in
    let result, start, finish =
      List.fold_left
        (fun (store, start, finish) -> function
           | Declaration.Chain { name; alternatives } ->
             let do_contributions = List.is_one alternatives in
             let without, ws = C.sink_to_dynarr ()
             and full, fs = C.sink_to_dynarr ()
             and reduced, rs = C.sink_to_dynarr () in
             let record = { without; full; reduced } in
             let reaction_driver = only_reaction ws
             and full_interval_driver = full_interval fs
             and start_driver, reduced_interval_driver = reduced_interval rs in
             let fanout_driver =
               C.fanout
                 [| reaction_driver; full_interval_driver; reduced_interval_driver |]
             in
             let rev_paths = List.map List.rev alternatives in
             let select = select_relevant_tokens ~cause ~conseq ~path:rev_paths in
             let preprocess =
               fun token ->
               let* token = select token in
               let contributions =
                 if do_contributions then Some (Token.contributions token) else None
               in
               Some (token, contributions)
             in
             let finish_driver token = Option.iter fanout_driver @@ preprocess token in
             ( ChainMap.add name record store
             , ChainMap.add name start_driver start
             , ChainMap.add name finish_driver finish )
           | _ -> store, start, finish)
        (ChainMap.empty, ChainMap.empty, ChainMap.empty)
        decl
    in
    let start probe = ChainMap.find probe start
    and finish probe = ChainMap.find probe finish in
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
