open Mrtccsl
open Prelude
open Analysis.FunctionalChain
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
module S = FnCh.ST
open Number.Rational
open FnCh.S.Session

let step = of_int 1 / of_int 1000

let priority_strategy priorities general_strategy =
  let priorities = A.L.of_list priorities in
  let f candidates =
    let candidates =
      List.stable_sort
        (fun (x, _) (y, _) ->
           Int.neg
           @@ Int.compare
                (A.L.cardinal (A.L.inter x priorities))
                (A.L.cardinal (A.L.inter y priorities)))
        candidates
    in
    let priotized, rest =
      List.partition (fun (l, _) -> A.L.cardinal (A.L.inter l priorities) > 0) candidates
    in
    if List.is_empty priotized then general_strategy rest else general_strategy priotized
  in
  f
;;

(*TODO: need to review if the priority strategy is really correct*)
(* let fifo_strategy priorities general_strategy =
  let queue = ref [] in
  let priorities = A.CMap.of_list priorities in
  let f candidates =
    let prioritized =
      !queue
      |> List.find_mapi (fun _ c ->
        match List.filter (fun (l, _) -> A.L.mem c l) candidates with
        | [] -> None
        | list -> Some list)
    in
    match
      Option.bind_or (Option.bind prioritized general_strategy) (fun _ ->
        general_strategy candidates)
    with
    | Some (label, _) as solution ->
      let _ =
        A.CMap.iter
          (fun r s ->
             if A.L.mem r label then queue := List.append !queue [ s ];
             if A.L.mem s label
             then (
               let _, new_queue =
                 List.map_inplace_or_drop (fun x -> if x = s then `Drop else `Skip) !queue
               in
               queue := new_queue))
          priorities
      in
      solution
    | None -> None
  in
  f
;; *)

let random_strat =
  S.Solution.avoid_empty
  @@ S.Solution.random_label
       (S.Num.random_leap
          ~upper_bound:(of_int 1000)
          ~ceil:(round_up step)
          ~floor:(round_down step)
          ~rand:random)
;;

(*
   module LSet = Set.Make (A.L)

let prioritize_single candidates =
  let labels = candidates |> Iter.map (fun (x, _) -> x) |> Iter.to_set (module LSet) in
  let candidates =
    Iter.filter
      (fun (l, _) ->
         A.L.cardinal l <= 1
         ||
         let ps =
           A.L.to_list l
           |> List.powerset_nz
           |> List.filter_map (fun l' ->
             let l' = A.L.of_list l' in
             if A.L.equal l l' then None else Some l')
         in
         not
           (List.exists
              (fun sub -> LSet.mem sub labels && LSet.mem (A.L.diff l sub) labels)
              ps))
      candidates
  in
  candidates
;; *)

let fast_strat =
  S.Solution.random_label @@ S.Num.fast ~upper_bound:(of_int 10) ~floor:(round_down step)
;;

open FnCh

let parallel_reaction_times
      ~sem
      ?(with_partial = false)
      params
      dist
      system_spec
      func_chain_spec
      runs
  =
  let _, _, horizon = params in
  let start, finish = chain_start_finish_clocks func_chain_spec in
  let body _ =
    let s, _, _, full_chains, partial_chains =
      FnCh.functional_chains ~sem params dist system_spec func_chain_spec
    in
    let full_reaction_times =
      FnCh.reaction_times s [ start, finish ] (Iter.of_dynarray full_chains)
    in
    if with_partial
    then
      partial_chains
      |> Iter.of_array
      |> Iter.flat_map Queue.to_iter
      |> Iter.map (fun (t : partial_chain) ->
        ( t.misses
          |> A.CMap.to_seq
          |> Seq.map (fun (k, v) -> S.Session.of_offset s k, v)
          |> Hashtbl.of_seq
        , [ start, finish ]
          |> List.to_seq
          |> Seq.map (fun (source, target) ->
            ( (source, target)
            , CMap.value ~default:horizon (S.Session.to_offset s target) t.trace
              - CMap.find (S.Session.to_offset s source) t.trace ))
          |> Hashtbl.of_seq ))
    else full_reaction_times
  in
  let pool = Domainslib.Task.setup_pool ~num_domains:8 () in
  Domainslib.Task.run pool (fun _ ->
    Domainslib.Task.parallel_for_reduce
      ~chunk_size:1
      ~start:0
      ~finish:runs
      ~body
      pool
      Iter.append
      Iter.empty)
;;

let dist = []

let func_chain_spec =
  Analysis.FunctionalChain.
    { first = "s.s"
    ; rest =
        [ `Causality, "s.f"
        ; `Causality, "c.s"
        ; `Causality, "c.f"
        ; `Sampling, "a.s"
        ; `Causality, "a.f"
        ]
    }
;;

let process name spec =
  let _ = Random.init 82763452 in
  let system_spec =
    Rtccsl.map_specification Fun.id Fun.id Fun.id Number.Rational.of_int spec
  in
  let strategy candidates = random_strat candidates in
  let steps = 1_000 in
  let horizon = of_int 20_000 in
  let simulations = 1_000 in
  let sem = Earliest in
  let massive = true in
  let points_of_interest = points_of_interest func_chain_spec in
  let reactions =
    if massive
    then
      parallel_reaction_times
        ~sem
        ~with_partial:false
        (strategy, steps, horizon)
        dist
        system_spec
        func_chain_spec
        simulations
    else (
      let s, trace, deadlock, chains, partial_chains =
        FnCh.functional_chains
          ~sem
          (strategy, steps, horizon)
          dist
          system_spec
          func_chain_spec
      in
      let chains = Iter.of_dynarray chains in
      let reactions = FnCh.reaction_times s points_of_interest chains in
      let _ = Printf.printf "deadlock: %b\n" deadlock in
      let _ =
        let trace_file = open_out (Printf.sprintf "./%s_trace.txt" name) in
        Export.trace_to_svgbob
          ~numbers:true
          ~precision:2
          ~tasks:Rtccsl.Examples.Macro.[ task_names "s"; task_names "c"; task_names "a" ]
          s
          (List.sort_uniq String.compare (Rtccsl.spec_clocks system_spec))
          (Format.formatter_of_out_channel trace_file)
          trace;
        close_out trace_file
      in
      let _ =
        Printf.printf
          "full chains:\n%s\n"
          (Iter.to_string
             ~sep:"\n"
             (fun (t : chain_instance) ->
                FnCh.CMap.to_string (of_offset s >> String.to_string) to_string t.trace)
             chains);
        Printf.printf
          "partial chains:\n%s\n"
          (Seq.to_string
             ~sep:"\n"
             (partial_chain_to_string s)
             (partial_chains |> Array.to_seq |> Seq.flat_map Queue.to_seq));
        Printf.printf
          "reaction times: %s"
          (FnCh.reaction_times_to_string ~sep:"\n" reactions)
      in
      let trace_file = open_out "./cadp_trace.txt" in
      let _ = Export.trace_to_csl s (Format.formatter_of_out_channel trace_file) trace in
      let _ = close_out trace_file in
      reactions)
  in
  let data_file = open_out (Printf.sprintf "./plots/data/%s_reaction_times.csv" name) in
  let _ =
      (FnCh.reaction_times_to_csv [ "a.s" ] points_of_interest data_file reactions)
  in
  close_out data_file
;;

let () =
  let use_cases =
    [ (* "certain1", Rtccsl.Examples.SimpleControl.no_resource_constraint_rigid_certain 15 2 5 5 2; *)
      ( "c2"
      , Rtccsl.Examples.SimpleControl.no_resource_constraint_rigid
          (14, 16)
          (1, 3)
          (2, 8)
          (4, 6)
          (1, 3) )
    ; ( "c3"
      , Rtccsl.Examples.SimpleControl.no_resource_constraint_rigid
          (14, 16)
          (1, 3)
          (2, 8)
          (14, 16)
          (1, 3) )
    ]
  in
  List.iter (fun (name, spec) -> process name spec) use_cases
;;
