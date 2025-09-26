open Prelude

module Chain = struct
  type relation =
    [ `Causality
    | `Sampling
    ]
  [@@deriving show, sexp]

  type 'c t =
    { first : 'c
    ; rest : (relation * 'c) list
    }
  [@@deriving map, show]

  let start_finish_clocks chain =
    ( chain.first
    , Option.value
        ~default:chain.first
        (Option.map (fun (_, c) -> c) (List.last chain.rest)) )
  ;;

  let links { first; rest } =
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
      ]
    [@@deriving show, sexp]

    let last_clock { first; rest } =
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
    let init = chain_spec.first, (`New : Instruction.t) in
    let rest_seq = chain_spec.rest |> List.map (fun (x, y) -> y, (x :> Instruction.t)) in
    init :: rest_seq
  ;;

  let parse str =
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
                  | None -> { first = next; rest = [] }
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

module Make (C : Automata.Simple.Hashed.ID) (N : Automata.Simple.Num) = struct
  module S = Automata.Simple.Hashed.WithSession (C) (N)
  module A = S.Inner
  module ST = Automata.Simple.Strategy (A)
  module CMap = Map.Make (A.C)
  open S.Session

  type chain_instance =
    { trace : N.t CMap.t
    ; misses : int CMap.t
    }
  [@@deriving map]

  type partial_chain =
    { trace : N.t CMap.t
    ; targets : int CMap.t
    ; mutable misses : int CMap.t
    }

  let partial_chain_to_string session chain =
    Printf.sprintf
      "trace: %s targets: %s misses: %s"
      (CMap.to_string (of_offset session >> C.to_string) N.to_string chain.trace)
      (CMap.to_string (of_offset session >> C.to_string) Int.to_string chain.targets)
      (CMap.to_string (of_offset session >> C.to_string) Int.to_string chain.misses)
  ;;

  type semantics =
    | All
    | Earliest
    | Lastest
    | Randomized

  let consume_label
        ?(sem = All)
        instructions
        (full_chains, (partial_chains : _ Queue.t array), counters)
        (label, now)
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
            { trace = CMap.singleton c now; targets; misses = CMap.empty }
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
                 Queue.add
                   { trace = CMap.add c now chain.trace
                   ; targets = chain.targets
                   ; misses = chain.misses
                   }
                   next;
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
              | Lastest ->
                let last = Queue.last candidates in
                Option.to_seq last
              | Randomized ->
                let el = Iter.sample 1 (Queue.to_iter candidates) in
                Seq.return el.(0)
            in
            let to_sample =
              Seq.map
                (fun chain ->
                   { trace = CMap.add c now chain.trace; targets; misses = chain.misses })
                to_sample
            in
            let next = partial_chains.(index) in
            Queue.add_seq next to_sample;
            Queue.clear candidates))
    in
    let _ = Array.iteri execute_instruction instructions in
    let new_full f a =
      let last = Array.length instructions - 1 in
      Queue.iter (fun chain -> f { trace = chain.trace; misses = chain.misses }) a.(last);
      Queue.clear a.(last)
    in
    let _ = Dynarray.append_iter full_chains new_full partial_chains in
    (* let _ = Printf.printf "dropped: %d\n" !dropped in *)
    full_chains, partial_chains, counters
  ;;

  let[@inline always] trace_to_chain sem chain trace =
    let instructions = Array.of_list (Chain.to_instructions chain) in
    let len_instr = Array.length instructions in
    let full_chains, dangling_chains, _ =
      Iter.fold
        (consume_label ~sem instructions)
        ( Dynarray.create ()
        , Array.init len_instr (fun _ -> Queue.create ())
        , Array.make len_instr 0 )
        trace
    in
    full_chains, dangling_chains
  ;;

  let functional_chains
        ?(debug = false)
        ?(sem = All)
        (s, n, time)
        (system_spec : _ Language.Specification.t)
        (chain : C.t Chain.t)
    =
    let session = create () in
    let env = A.of_spec ~debug (with_spec session system_spec) in
    let trace, cut =
      A.gen_trace s env |> A.Trace.take ~steps:n |> A.Trace.until ~horizon:time
    in
    let trace = A.Trace.persist ~size_hint:n trace in
    let session_chain = Chain.map (to_offset session) chain in
    let full_chains, dangling_chains =
      trace_to_chain sem session_chain (A.Trace.to_iter trace)
    in
    (* let _ =
      Printf.printf "There are %i dangling chains.\n" (List.length dangling_chains);
      Printf.printf
        "%s\n"
        (List.to_string ~sep:"\n" partial_chain_to_string dangling_chains)
    in *)
    session, trace, not !cut, full_chains, dangling_chains
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

  let print_statistics session category formatter chains =
    let stats = statistics category chains in
    let total = Iter.fold (fun total (_, x) -> total + x) 0 stats in
    Format.fprintf
      formatter
      "%s | total: %i\n"
      (C.to_string (of_offset session category))
      total;
    let total = Float.of_int total in
    Format.fprintf
      formatter
      "%a"
      (Iter.pp_seq ~sep:"" (fun formatter (c, x) ->
         Format.fprintf formatter "%i | %f\n" c (Float.of_int x /. total)))
      stats;
    Format.pp_print_flush formatter ()
  ;;

  let categorized_reaction_times session categories span chain_instances =
    let misses_into_category map =
      List.to_string
        ~sep:"_"
        (fun sample ->
           let missed = CMap.find_opt sample map in
           let missed = Option.value ~default:0 missed in
           Printf.sprintf "%s=%i" (of_offset session sample) missed)
        categories
    in
    let reaction_times =
      Iter.map
        (fun ({ misses; _ } as chain : chain_instance) ->
           misses_into_category misses, reaction_time_of_span chain span)
        chain_instances
    in
    reaction_times
  ;;

  let reaction_times_to_string ~sep iter =
    Iter.to_string
      ~sep
      (fun (_, t) ->
         t
         |> Hashtbl.to_seq
         |> Seq.to_string (fun ((s, f), v) ->
           Printf.sprintf "(%s, %s) -> %s" (C.to_string s) (C.to_string f) (N.to_string v)))
      iter
  ;;

  let reaction_times_to_csv session categories pairs_to_print iter ch =
    Printf.fprintf
      ch
      "%s\n"
      (List.to_string
         ~sep:","
         Fun.id
         (List.map
            (fun (f, s) ->
               Printf.sprintf "%s->%s" (of_offset session f) (of_offset session s))
            pairs_to_print
          @ List.map (of_offset session) categories));
    Iter.iter
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

  module Export = struct
    module Set = Set.Make (String)
    module Inner = Automata.Export.Make (String) (N) (Set)

    let convert_tasks session tasks =
      List.map (Automata.Export.map_task @@ of_offset session) tasks
    ;;

    let convert_trace session trace =
      Iter.map
        (fun (l, n) -> l |> A.L.to_iter |> Iter.map (of_offset session) |> Set.of_iter, n)
        trace
    ;;

    let trace_to_svgbob ?numbers ?precision ~tasks session clocks ch trace =
      Inner.Svgbob.print_horizontal
        ?numbers
        ?precision
        ~tasks:(convert_tasks session tasks)
        clocks
        ch
        (convert_trace session trace)
    ;;

    let trace_to_vertical_svgbob ?numbers ~tasks session clocks channel trace =
      Inner.Svgbob.print_vertical
        ?numbers
        ~tasks:(convert_tasks session tasks)
        clocks
        channel
        (convert_trace session trace)
    ;;

    let trace_to_cadp session ch trace =
      Inner.CSL.print
        ~step_sep:",STEP,"
        ~tagger:Inner.Tag.none
        ~serialize:Inner.Serialize.random
        ch
        (convert_trace session trace)
    ;;

    let trace_to_timed_cadp session round_to order_hints ch trace =
      Inner.CSL.print
        ~tagger:(Inner.Tag.tag_round_timestamp round_to)
        ~serialize:(Inner.Serialize.respect_microstep order_hints)
        ch
        (convert_trace session trace)
    ;;
  end
end
