open Prelude

module Chain = struct
  type relation =
    [ `Causality
    | `Sampling
    ]
  [@@deriving show, sexp]

  type 'c t =
    { first : 'c
    ; periodic : bool
    ; rest : (relation * 'c) list
    }
  [@@deriving map, show]

  let start_finish_clocks chain =
    ( chain.first
    , Option.value
        ~default:chain.first
        (Option.map (fun (_, c) -> c) (List.last chain.rest)) )
  ;;

  let links { first; rest; _ } =
    let _, links =
      List.fold_left
        (fun (prev, links) (_, next) -> next, (prev, next) :: links)
        (first, [])
        rest
    in
    List.rev links
  ;;

  let spans_of_interest chain = start_finish_clocks chain :: links chain

  let sampling_clocks chain =
    List.filter_map
      (fun (rel, next) ->
         match rel with
         | `Sampling -> Some next
         | _ -> None)
      chain.rest
  ;;

  module Instruction = struct
    type t =
      [ relation
      | `New
      | `NewPeriodic
      ]
    [@@deriving show, sexp]

    let last_clock { first; rest; _ } =
      Option.value ~default:first (List.last (List.map (fun (_, x) -> x) rest))
    ;;

    let pp pp_f f =
      Format.fprintf f "[@[%a@]]"
      @@ Format.pp_print_list
           ~pp_sep:(fun f () -> Format.fprintf f "@;")
           (fun f (s, i) -> Format.fprintf f "%a, %a" pp_f s pp i)
    ;;
  end

  let to_instructions chain_spec =
    let init =
      ( chain_spec.first
      , if chain_spec.periodic then `NewPeriodic else (`New : Instruction.t) )
    in
    let rest_seq = chain_spec.rest |> List.map (fun (x, y) -> y, (x :> Instruction.t)) in
    init :: rest_seq
  ;;

  let parse str =
    let periodic, str =
      match String.chop_prefix ~pre:"~" str with
      | Some str -> true, str
      | None -> false, str
    in
    let causalities = String.split ~by:"->" str in
    let with_sampling = List.map (String.split ~by:"?") causalities in
    let r =
      Seq.fold_left
        (fun chain samples ->
           Seq.fold_lefti
             (fun chain i next ->
                let r =
                  match chain with
                  | Some chain ->
                    { chain with
                      rest =
                        List.append
                          chain.rest
                          [ (if i = 0 then `Causality, next else `Sampling, next) ]
                    }
                  | None -> { first = next; periodic; rest = [] }
                in
                Some r)
             chain
             (List.to_seq samples))
        None
        (List.to_seq with_sampling)
    in
    Option.get r
  ;;

  let parse_with_name str =
    match String.split ~by:":" str with
    | [ name; chain ] -> name, parse chain
    | _ ->
      failwith
        (Printf.sprintf
           "invalid chain \"%s\", should follow the template <name>:<chain \
            link>((->|?)<chain link>)*"
           str)
  ;;

  let parse_from_channel ch = ch |> In_channel.lines_seq |> Seq.map parse_with_name
end

module Make
    (C : Backend.Naive.Hashed.ID)
    (N : sig
       include Backend.Naive.Num

       val ( / ) : t -> t -> t
     end) =
struct
  module A = Backend.Naive.Make (C) (N)
  module ST = Backend.Naive.Strategy (A)
  module CMap = Map.Make (A.C)
  module Trace = Trace.MakeIO (N) (A.L)

  type chain_instance =
    { trace : N.t CMap.t
    ; misses : int CMap.t
    ; since : N.t option
    }
  [@@deriving map]

  type partial_chain =
    { trace : N.t CMap.t
    ; targets : int CMap.t
    ; mutable misses : int CMap.t
    ; since : N.t option
    }

  let partial_chain_to_string chain =
    Printf.sprintf
      "trace: %s targets: %s misses: %s"
      (CMap.to_string C.to_string N.to_string chain.trace)
      (CMap.to_string C.to_string Int.to_string chain.targets)
      (CMap.to_string C.to_string Int.to_string chain.misses)
  ;;

  type semantics =
    | All
    | Earliest
    | Latest
    | Randomized

  let consume_label
        ?(sem = All)
        ~update_tick
        instructions
        (full_chains, (partial_chains : _ Queue.t array), counters)
        Trace.{ label; time = now }
    =
    let targets_from i =
      let chain_target = Array.get counters i in
      let targets, _ =
        instructions
        |> Iter.of_array
        |> Iter.foldi
             (fun (targets, met_sampling) j (c, instr) ->
                match met_sampling, instr with
                | false, `Causality when j > i -> CMap.add c chain_target targets, false
                | _, `Sampling when j > i -> targets, true
                | _ -> targets, met_sampling)
             (CMap.empty, false)
      in
      targets
    in
    let _ =
      Array.mapi_inplace
        (fun i current ->
           let c, _ = Array.get instructions i in
           let current = current + if A.L.mem c label then 1 else 0 in
           current)
        counters
    in
    let add_missed i k =
      for j = 0 to pred i do
        Queue.iter
          (fun c -> c.misses <- CMap.entry (fun v -> v + 1) ~default:0 k c.misses)
          partial_chains.(j)
      done
    in
    (* let dropped = ref 0 in *)
    let execute_instruction index (c, instr) =
      if A.L.mem c label
      then (
        match instr with
        | `New ->
          let targets = targets_from index in
          Queue.add
            { trace = CMap.singleton c now; targets; misses = CMap.empty; since = None }
            partial_chains.(0)
        | `NewPeriodic ->
          let targets = targets_from index in
          let since = update_tick c now in
          Queue.add
            { trace = CMap.singleton c now
            ; targets
            ; misses = CMap.empty
            ; since = Some since
            }
            partial_chains.(0)
        | `Causality ->
          let q = partial_chains.(index - 1) in
          let next = partial_chains.(index) in
          let counter = counters.(index) in
          let rec aux q =
            match Queue.peek_opt q with
            | Some chain ->
              (match CMap.find_opt c chain.targets with
               | Some target when target = counter ->
                 Queue.add { chain with trace = CMap.add c now chain.trace } next;
                 Queue.drop q;
                 aux q
               | _ -> ())
            | None -> ()
          in
          aux q
        | `Sampling ->
          let targets = targets_from index in
          let candidates = partial_chains.(index - 1) in
          add_missed (index - 1) c;
          if not (Queue.is_empty candidates)
          then (
            let to_sample =
              match sem with
              | All -> Queue.to_seq candidates
              | Earliest ->
                let first = Queue.peek_opt candidates in
                Option.to_seq first
              | Latest ->
                let last = Queue.last candidates in
                Option.to_seq last
              | Randomized ->
                let el = Iter.sample 1 (Queue.to_iter candidates) in
                Seq.return el.(0)
            in
            let to_sample =
              Seq.map
                (fun chain -> { chain with trace = CMap.add c now chain.trace; targets })
                to_sample
            in
            let next = partial_chains.(index) in
            Queue.add_seq next to_sample;
            Queue.clear candidates))
    in
    let _ = Array.iteri execute_instruction instructions in
    let new_full f a =
      let last = Array.length instructions - 1 in
      Queue.iter
        (fun chain ->
           f { trace = chain.trace; misses = chain.misses; since = chain.since })
        a.(last);
      Queue.clear a.(last)
    in
    let _ = Dynarray.append_iter full_chains new_full partial_chains in
    (* let _ = Printf.printf "dropped: %d\n" !dropped in *)
    full_chains, partial_chains, counters
  ;;

  let[@inline always] extract_chains sem chain trace =
    let instructions = Array.of_list (Chain.to_instructions chain) in
    let len_instr = Array.length instructions in
    let ticks = ref CMap.empty in
    let update_tick clock time =
      let previous = CMap.value ~default:N.zero clock !ticks in
      ticks := CMap.add clock time !ticks;
      previous
    in
    let full_chains, dangling_chains, _ =
      Seq.fold_left
        (consume_label ~update_tick ~sem instructions)
        ( Dynarray.create ()
        , Array.init len_instr (fun _ -> Queue.create ())
        , Array.make len_instr 0 )
        trace
    in
    full_chains, dangling_chains
  ;;

  let chains_of_spec
        ?(debug = false)
        ?(sem = All)
        (s, n, time)
        (system_spec : _ Language.Specification.t)
        (chain : C.t Chain.t)
    =
    let env = A.of_spec ~debug system_spec in
    let trace, cut =
      A.gen_trace s env |> Trace.take ~steps:n |> Trace.until ~horizon:time
    in
    let trace = Trace.persist ~size_hint:n trace in
    let full_chains, dangling_chains = extract_chains sem chain trace in
    (* let _ =
      Printf.printf "There are %i dangling chains.\n" (List.length dangling_chains);
      Printf.printf
        "%s\n"
        (List.to_string ~sep:"\n" partial_chain_to_string dangling_chains)
    in *)
    trace, not !cut, full_chains, dangling_chains
  ;;

  let reaction_time_of_span ({ trace; _ } : chain_instance) (first, last) : N.t =
    N.(CMap.find last trace - CMap.find first trace)
  ;;

  let statistics category chains =
    let module IMap = Map.Make (Int) in
    chains
    |> Iter.fold
         (fun acc ({ misses; _ } : chain_instance) ->
            IMap.entry
              ~default:0
              (Int.add 1)
              (Option.value ~default:0 (CMap.find_opt category misses))
              acc)
         IMap.empty
    |> IMap.to_iter
    |> Iter.persistent
  ;;

  let print_statistics category formatter chains =
    let stats = statistics category chains in
    let total = Iter.fold (fun total (_, x) -> total + x) 0 stats in
    Format.fprintf formatter "%s | total: %i\n" (C.to_string category) total;
    let total = Float.of_int total in
    Format.fprintf
      formatter
      "%a"
      (Iter.pp_seq ~sep:"" (fun formatter (c, x) ->
         Format.fprintf formatter "%i | %f\n" c (Float.of_int x /. total)))
      stats;
    Format.pp_print_flush formatter ()
  ;;

  let categorized_reaction_times categories span chain_instances =
    let misses_into_category map =
      List.to_string
        ~sep:"_"
        (fun sample ->
           let missed = CMap.find_opt sample map in
           let missed = Option.value ~default:0 missed in
           Printf.sprintf "%s=%i" (C.to_string sample) missed)
        categories
    in
    let reaction_times =
      Seq.map
        (fun ({ misses; _ } as chain : chain_instance) ->
           misses_into_category misses, reaction_time_of_span chain span)
        chain_instances
    in
    reaction_times
  ;;

  (**[weighted_full_reaction_times ~discretize_range chain chain_instances] returns end-to-end reaction time of the functional [chain] using [~discretize_range] to randomly offset the reaction times, inside [(0, start[i+1]-start[i])] range.*)
  let weighted_full_reaction_times ?discretize_range chain chain_instances =
    let open Chain in
    let span = start_finish_clocks chain in
    let links = links chain in
    let reaction_times =
      Seq.flat_map
        (fun chain ->
           let total = reaction_time_of_span chain span in
           let contributions =
             links
             |> List.map (fun span ->
               let f, s = span in
               let name = Printf.sprintf "%s->%s" (C.to_string f) (C.to_string s) in
               name, reaction_time_of_span chain span)
           in
           let compute_wights contributions total =
             List.map
               (fun (name, link_reaction) ->
                  name, if N.equal total N.zero then N.zero else N.(link_reaction / total))
               contributions
           in
           let reactions =
             match chain.since with
             | Some since ->
               let blind_range = N.(CMap.find (fst span) chain.trace - since) in
               (match discretize_range with
                | Some discretize_range ->
                  let blind_spots = discretize_range blind_range in
                  (*"blind spot" here is an uncertain region of time between the period ticks*)
                  Seq.map
                    (fun blind_spot ->
                       let total = N.(blind_spot + total) in
                       let contributions = ("blind_spot", blind_spot) :: contributions in
                       contributions, total)
                    blind_spots
                | None ->
                  let total = N.(blind_range + total) in
                  let contributions = ("blind_spot", blind_range) :: contributions in
                  Seq.return (contributions, total))
             | None -> Seq.return (contributions, total)
           in
           Seq.map
             (fun (contributions, total) -> compute_wights contributions total, total)
             reactions)
        chain_instances
    in
    reaction_times
  ;;

  let reaction_times_to_string ~sep iter =
    Seq.to_string
      ~sep
      (fun (_, t) ->
         t
         |> Hashtbl.to_seq
         |> Seq.to_string (fun ((s, f), v) ->
           Printf.sprintf "(%s, %s) -> %s" (C.to_string s) (C.to_string f) (N.to_string v)))
      iter
  ;;

  let reaction_times_to_csv categories pairs_to_print iter ch =
    Printf.fprintf
      ch
      "%s\n"
      (List.to_string
         ~sep:","
         Fun.id
         (List.map
            (fun (f, s) -> Printf.sprintf "%s->%s" (C.to_string f) (C.to_string s))
            pairs_to_print
          @ List.map C.to_string categories));
    Seq.iter
      (fun ({ misses; _ } as chain : chain_instance) ->
         Printf.fprintf
           ch
           "%s\n"
           (List.to_string
              ~sep:","
              Fun.id
              (List.map
                 (fun span -> N.to_string @@ reaction_time_of_span chain span)
                 pairs_to_print
               @ List.map
                   (fun h ->
                      let v = Option.value ~default:0 (CMap.find_opt h misses) in
                      Int.to_string v)
                   categories)))
      iter
  ;;
end
