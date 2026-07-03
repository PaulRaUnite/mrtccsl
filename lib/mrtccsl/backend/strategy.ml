open Common
open Prelude

module type L = sig
  type t

  val is_empty : t -> bool
  val cardinal : t -> int
end

module type N = sig
  type t

  val zero : t
  val ( + ) : t -> t -> t
end

module Num (N : N) (NI : Interval.I with type num = N.t) = struct
  type t = NI.t -> NI.num

  let bounded bound lin_cond =
    assert (NI.subset bound (NI.pinf N.zero));
    let choice = NI.inter lin_cond bound in
    if NI.is_empty choice then None else Some choice
  ;;

  let random_leap ~upper_bound ~ceil ~floor ~rand cond =
    let left_bound = Option.value ~default:N.zero (NI.left_bound_opt cond) in
    let cond =
      if NI.is_right_unbound cond
      then NI.inter cond NI.(left_bound =-= N.(left_bound + upper_bound))
      else cond
    in
    let x, y =
      match cond with
      | NI.Bound (NI.Include x, NI.Include y) -> x, y
      | NI.Bound (NI.Exclude x, NI.Include y) -> ceil x y, y
      | NI.Bound (NI.Include x, NI.Exclude y) -> x, floor x y
      | NI.Bound (NI.Exclude x, NI.Exclude y) -> ceil x y, floor x y
      | _ -> invalid_arg "random on infinite interval is not supported"
    in
    rand x y
  ;;

  let slow ~upper_bound ~ceil cond =
    let left_bound = Option.value ~default:N.zero (NI.left_bound_opt cond) in
    let cond = NI.inter cond NI.(left_bound =-= N.(left_bound + upper_bound)) in
    match cond with
    | NI.Bound (NI.Include x, _) -> x
    | NI.Bound (NI.Exclude x, NI.Include y) | NI.Bound (NI.Exclude x, NI.Exclude y) ->
      ceil x y
    | _ -> invalid_arg "random on infinite interval is not supported"
  ;;

  let fast ~upper_bound ~floor cond =
    let left_bound = Option.value ~default:N.zero (NI.left_bound_opt cond) in
    let cond = NI.inter cond NI.(left_bound =-= N.(left_bound + upper_bound)) in
    match cond with
    | NI.Bound (NI.Include _, NI.Include y) | NI.Bound (NI.Exclude _, NI.Include y) -> y
    | NI.Bound (NI.Include x, NI.Exclude y) | NI.Bound (NI.Exclude x, NI.Exclude y) ->
      floor x y
    | _ -> invalid_arg "random on infinite interval is not supported"
  ;;

  let fast_and_slow ~upper_bound ~ceil ~floor cond =
    if Random.bool () then slow ~upper_bound ~ceil cond else fast ~upper_bound ~floor cond
  ;;
end

module Solution (L : L) (NI : Interval.I) = struct
  type guard = L.t * NI.t
  type solution = L.t * NI.num
  type t = guard -> solution option

  let first num_decision variants =
    let non_empty_first =
      variants
      |> Iter.find_map (fun (l, c) ->
        if L.is_empty l then None else Some (l, num_decision c))
    in
    let any_first () =
      let* l, c = Iter.head variants in
      Some (l, num_decision c)
    in
    Option.bind_or non_empty_first any_first
  ;;

  let weighted_label num_decision solutions =
    let solutions = Iter.to_array solutions in
    if Array.length solutions = 0
    then None
    else (
      let assign_weight ((label, _) as sol) = sol, L.cardinal label in
      let weighted = Array.map assign_weight solutions in
      let max_weight =
        Array.fold_left (fun max (_, w) -> Int.max max (Int.succ w)) 1 weighted
      in
      let weighted = Array.map (fun (sol, w) -> sol, max_weight - w) weighted in
      let weight_sum = Array.fold_left (fun sum (_, weight) -> sum + weight) 0 weighted in
      let choice = Random.int weight_sum in
      let sol, _ =
        (Array.fold_left (fun (chosen, sum) (sol, weight) ->
           match chosen with
           | Some choice -> Some choice, sum
           | None ->
             let sum = sum - weight in
             if sum <= 0 then Some sol, sum else None, sum))
          (None, choice)
          weighted
      in
      let label, bound =
        Option.unwrap ~expect:"weighted_label: choice should not fail" sol
      in
      let time = num_decision bound in
      Some (label, time))
  ;;

  let random_label num_decision solutions =
    let solutions = Iter.to_array solutions in
    if Array.length solutions = 0
    then None
    else (
      let len = Array.length solutions in
      let choice = Random.int len in
      let l, c = Array.get solutions choice in
      let n = num_decision c in
      Some (l, n))
  ;;

  let avoid_empty s variants =
    let empty = Iter.filter (fun (l, _) -> L.is_empty l) variants
    and non_empty = Iter.filter (fun (l, _) -> not (L.is_empty l)) variants in
    Option.bind_or (s non_empty) (fun () -> s empty)
  ;;

  let refuse_empty s variants =
    let variants = Iter.filter (fun (l, _) -> not (L.is_empty l)) variants in
    s variants
  ;;
  (*
       let debug f variants =
      let _ = Printf.printf "variants at strategy: %s\n" (guard_to_string variants) in
      f variants
    ;; *)
end
