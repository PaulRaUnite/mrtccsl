module type ID = sig
  include Set.OrderedType
end

module type Simple = sig
  type clock
  type num
  type label
  type num_cond
  type guard = (label list * num_cond) list
  type solution = label * num
  type strategy = guard -> solution
  type trace = solution list
  type t = (unit -> guard) * (solution -> unit) * label

  val empty : t
  val step : t -> strategy -> solution option
  val run : t -> strategy -> int -> trace
  val synchronize : t -> t -> t
  val constr_to_automata : clock Rtccsl.constr -> t
  val spec_to_automata : clock Rtccsl.specification -> t
end

let ( let* ) = Option.bind

module type Num = sig
  include Interval.Num

  val zero : t
end

module MakeSimple (C : ID) (N : Num) : Simple = struct
  type clock = C.t
  type num = N.t

  module ClockSet = Set.Make (C)
  module I = Interval.Make (N)

  type label = ClockSet.t
  type num_cond = I.t
  type guard = (label list * num_cond) list
  type solution = label * num
  type strategy = guard -> solution
  type trace = solution list
  type t = (unit -> guard) * (solution -> unit) * label

  let empty = (fun () -> [ [ ClockSet.empty ], I.inf ]), (fun _ -> ()), ClockSet.empty

  let step (a : t) (s : strategy) : solution option =
    let guards, transition, _ = a in
    let possible = guards () in
    if Misc.empty possible
    then None
    else (
      let sol = s possible in
      let () = transition sol in
      Some sol)
  ;;

  let run a s n : solution list =
    let rec aux a s n l =
      if n = 0
      then l
      else (
        match step a s with
        | None -> l
        | Some r -> aux a s (n - 1) (l @ [ r ]))
    in
    aux a s n []
  ;;

  let synchronize (a1 : t) (a2 : t) : t =
    let g1, t1, c1 = a1 in
    let g2, t2, c2 = a2 in
    let c = ClockSet.union c1 c2 in
    let conf_surface = ClockSet.inter c1 c2 in
    let sat_solver (l, l') =
      if ClockSet.equal (ClockSet.inter conf_surface l) (ClockSet.inter conf_surface l')
      then Some (ClockSet.union l l')
      else None
    in
    let linear_solver c c' =
      let res = I.inter (I.pinf N.zero) (I.inter c c') in
      if I.is_empty res then None else Some res
    in
    let guard_solver ((l, c), (l', c')) =
      match linear_solver c c' with
      | None -> None
      | Some s ->
        let r = List.filter_map sat_solver (Misc.cartesian l l') in
        if Misc.empty r then None else Some (r, s)
    in
    let g () = List.filter_map guard_solver (Misc.cartesian (g1 ()) (g2 ())) in
    let t l =
      t1 l;
      t2 l
    in
    g, t, c
  ;;

  open Rtccsl

  (*stolen from https://stackoverflow.com/questions/40141955/computing-a-set-of-all-subsets-power-set*)
  let rec powerset = function
    | [] -> [ [] ]
    | x :: xs ->
      let ps = powerset xs in
      ps @ List.map (fun ss -> x :: ss) ps
  ;;

  let simple_guard l = [ l, I.inf ]

  let prec c1 c2 strict =
    let c = ref 0 in
    ( (fun () ->
        let l = List.map ClockSet.of_list (powerset [ c1; c2 ]) in
        let l =
          if !c = 0
          then
            List.filter
              (fun x ->
                if strict
                then not @@ ClockSet.mem c2 x
                else not ((not @@ ClockSet.mem c1 x) && ClockSet.mem c2 x))
              l
          else l
        in
        simple_guard l)
    , (fun (l, _) ->
        let delta = if ClockSet.mem c1 l then 1 else 0 in
        let delta = delta - if ClockSet.mem c2 l then 1 else 0 in
        c := !c + delta)
    , ClockSet.of_list [ c1; c2 ] )
  ;;

  let constr_to_automata (c : clock Rtccsl.constr) : t =
    match c with
    | Precedence (c1, c2) -> prec c1 c2 true
    | Causality (c1, c2) -> prec c1 c2 false
    | _ -> failwith "not implemented"
  ;;

  (*
     | Causality (_, _) -> _
     | Exclusion _ -> _
     | Coincidence _ -> _
     | Subclocking (_, _) -> _
     | Minus (_, _, _) -> _
     | Delay (_, _, _, _) -> _
     | Fastest (_, _) -> _
     | Slowest (_, _) -> _
     | Intersection (_, _) -> _
     | Union (_, _) -> _
     | Periodic (_, _, _) -> _
     | Sample (_, _, _) -> _
     | Alternate (_, _) -> _
     | RTdelay (_, _) -> _
     | CumulPeriodic (_, _) -> _
     | AbsPeriodic (_, _) -> _
     | FirstSampled (_, _, _) -> _
     | LastSampled (_, _, _) -> _
     | Forbid (_, _, _) -> _
     | Allow (_, _, _) -> _
     | Sporadic (_, _) -> _ *)
  let spec_to_automata spec =
    List.fold_left synchronize empty (List.map constr_to_automata spec)
  ;;
end
