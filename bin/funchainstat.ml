open Mrtccsl
open Prelude
module FnCh = Analysis.FunctionalChain.Make (String) (Number.Rational)
module A = FnCh.A
open Number.Rational

let step = of_int 1 / of_int 10

let priority_strategy priorities general_strategy =
  let priorities = A.L.of_list priorities in
  let f candidates =
    let candidates =
      List.sort
        (fun (x, _) (y, _) -> Int.compare (A.L.cardinal x) (A.L.cardinal y))
        candidates
    in
    match
      List.find_opt (fun (l, _) -> not (A.L.is_empty (A.L.inter l priorities))) candidates
    with
    | Some (label, cond) ->
      (* Printf.printf "prioritized: %s \n" (A.guard_to_string (label, cond)); *)
      let* d =
        A.Strategy.random_leap (of_int 10) (round_up step) (round_down step) random cond
      in
      Some (label, d)
    | None -> general_strategy candidates
  in
  f
;;

let random_strat =
  A.Strategy.random_label
    ~avoid_empty:true
    10
    (A.Strategy.random_leap (of_int 100) (round_up step) (round_down step) random)
;;

let fast_strat =
  A.Strategy.random_label 10
  @@ A.Strategy.fast (A.I.make_include (of_int 0) (of_int 10)) (round_down step)
;;

let one = of_int 1
let two = of_int 2
let hundred = of_int 100
let half = Rational.(of_int 1 / of_int 2)

let task_clocks name =
  let start = Printf.sprintf "%s.s" name in
  let finish = Printf.sprintf "%s.f" name in
  let ready = Printf.sprintf "%s.r" name in
  let deadline = Printf.sprintf "%s.d" name in
  name, ready, start, finish, deadline
;;

let task name exec_duration =
  let _, ready, start, finish, _ = task_clocks name in
  Rtccsl.
    [ Causality { cause = ready; conseq = start }
    ; RTdelay
        { out = finish
        ; arg = start
        ; delay = Tuple.map2 (fun x -> TimeConst (of_int x)) exec_duration
        }
    ]
;;

let task_with_deadline name exec_duration deadline =
  let finish = Printf.sprintf "%s.f" name in
  Rtccsl.Precedence { cause = finish; conseq = deadline } :: task name exec_duration
;;

let periodic_task name exec_duration period error =
  let ready = Printf.sprintf "%s.r" name in
  let timer = Printf.sprintf "%s.t" name in
  let deadline = Printf.sprintf "%s.d" name in
  task_with_deadline name exec_duration deadline
  @ Rtccsl.
      [ CumulPeriodic
          { out = timer
          ; period = TimeConst (of_int period)
          ; error = TimeConst (of_int (Int.neg error)), TimeConst (of_int error)
          ; offset = TimeConst zero
          }
      ; Delay
          { out = deadline
          ; arg = timer
          ; delay = IntConst 1, IntConst 1
          ; base = Some timer
          }
      ; Coincidence [ timer; ready ]
      ]
;;

let scheduling_pairs tasks =
  List.map
    (fun name ->
       let _, _, start, finish, _ = task_clocks name in
       start, finish)
    tasks
;;

let parallel_reaction_times params system_spec func_chain_spec runs =
  let pool = Domainslib.Task.setup_pool ~num_domains:8 () in
  let body _ =
    let _, chains = FnCh.functional_chains params system_spec func_chain_spec in
    FnCh.reaction_times "s.t" "a.f" chains
  in
  Domainslib.Task.run pool (fun _ ->
    Domainslib.Task.parallel_for_reduce
      ~chunk_size:1
      ~start:0
      ~finish:runs
      ~body
      pool
      Seq.append
      Seq.empty)
;;

let () =
  let _ = Random.init 2376478236472 in
  let system_spec =
    List.flatten
      Rtccsl.
        [ [ Pool (2, scheduling_pairs [ "a"; "s"; "c" ]) ]
        (* ; [ Alternate { first = "a.s"; second = "a.f" }
          ; Alternate { first = "s.s"; second = "s.f" }
          ; Alternate { first = "c.s"; second = "c.f" }
          ] *)
        ; periodic_task "s" (10, 15) 50 2
        ; periodic_task "a" (5, 10) 50 2
        ; task "c" (25, 40)
        ; [ Coincidence [ "s.f"; "c.r" ] ]
        ]
  in
  let func_chain_spec =
    FnCh.
      { first = "s.t"
      ; rest =
          [ `Causality, "s.s"
          ; `Causality, "s.f"
          ; `Causality, "c.s"
          ; `Causality, "c.f"
          ; `Sampling, "a.s"
          ; `Causality, "a.f"
          ]
      }
  in
  let strategy = priority_strategy [ "s.s"; "c.s"; "a.s" ] random_strat in
  let steps = 10_000 in
  let horizon = of_int 10_000 in
  let reactions =
    parallel_reaction_times (strategy, steps, horizon) system_spec func_chain_spec 100
  in
  (* let svgbob_str =
    A.trace_to_svgbob
      ~numbers:true
      ~tasks:[ task_clocks "s"; task_clocks "c"; task_clocks "a" ]
      (List.sort_uniq String.compare (Rtccsl.spec_clocks system_spec))
      trace
  in
  let _ =
    print_endline svgbob_str;
    Format.printf
      "chains:\n%s\n"
      (Seq.to_string ~sep:"\n" (FnCh.CMap.to_string String.to_string to_string) chains);
    Format.printf "reaction times: %s\n" (Seq.to_string to_string reactions)
  in *)
  (* let trace_file = open_out "./cadp_trace.txt" in
  let _ = Printf.fprintf trace_file "%s" (A.trace_to_csl trace) in
  let _ = close_out trace_file in *)
  let data_file = open_out "./plots/data/reaction_times.txt" in
  let _ = Printf.fprintf data_file "%s" (FnCh.reaction_times_to_string reactions) in
  close_out data_file
;;
