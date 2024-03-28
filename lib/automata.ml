open Prelude

module type ID = sig
  include Set.OrderedType
end

module type Simple = sig
  type clock
  type num
  type label
  type num_cond
  type guard = (label * num_cond) list
  type solution = label * num
  type strategy = guard -> solution option
  type trace = solution list
  type t = (unit -> guard) * (solution -> bool) * label

  module I : Interval.I
  module L : Set.S

  val empty : t
  val step : strategy -> t -> solution option
  val run : strategy -> t -> int -> trace
  val bisimulate : strategy -> t -> t -> int -> (trace, trace) result
  val sync : t -> t -> t
  val of_constr : clock Rtccsl.constr -> t
  val of_spec : clock Rtccsl.specification -> t

  module Strategy : sig
    val first : (num_cond -> num option) -> strategy
    val slow : num_cond -> num_cond -> num option
    val fast : num_cond -> num_cond -> num option
  end
end

module type Num = sig
  include Interval.Num
  include ExpOrder.T with type t := t

  val zero : t
end

module MakeSimple (C : ID) (N : Num) = struct
  type clock = C.t
  type num = N.t

  module L = Set.Make (C)
  module I = Interval.Make (N)

  type label = L.t
  type num_cond = I.t
  type guard = (label * num_cond) list
  type solution = label * num
  type strategy = guard -> solution option
  type trace = solution list
  type t = (unit -> guard) * (solution -> bool) * label

  let empty : t = (fun () -> [ L.empty, I.inf ]), (fun _ -> true), L.empty

  let step s (a : t) : solution option =
    let guards, transition, _ = a in
    let possible = guards () in
    if is_empty possible
    then None
    else
      let* sol = s possible in
      if transition sol then Some sol else None
  ;;

  let run s (a : t) n : solution list = collect n (fun () -> step s a)

  let sync (a1 : t) (a2 : t) : t =
    let g1, t1, c1 = a1 in
    let g2, t2, c2 = a2 in
    let c = L.union c1 c2 in
    let conf_surface = L.inter c1 c2 in
    let sat_solver l l' =
      if L.is_empty conf_surface
         || L.equal (L.inter conf_surface l) (L.inter conf_surface l')
      then Some (L.union l l')
      else None
    in
    let linear_solver c c' =
      let res = I.inter (I.pinf N.zero) (I.inter c c') in
      if I.is_empty res then None else Some res
    in
    let guard_solver ((l, c), (l', c')) =
      let* l = sat_solver l l'
      and* c = linear_solver c c' in
      Some (l, c)
    in
    let g () =
      let g1 = g1 () in
      let g2 = g2 () in
      List.filter_map guard_solver @@ cartesian g1 g2
    in
    let t l = t1 l && t2 l in
    g, t, c
  ;;

  open Rtccsl

  let simple_guard l : guard = List.map (fun l -> l, I.pinf N.zero) l

  let stateless labels clocks : t =
    let g = simple_guard labels in
    ( (fun () -> g)
    , (fun (l', n) -> List.mem l' labels && N.more n N.zero)
    , L.of_list clocks )
  ;;

  let prec c1 c2 strict : t =
    let c = ref 0 in
    let l1 = List.map L.of_list (powerset [ c1; c2 ]) in
    let l2 =
      List.filter
        (fun x ->
          if strict then not @@ L.mem c2 x else not ((not @@ L.mem c1 x) && L.mem c2 x))
        l1
    in
    ( (fun () ->
        let l = if !c = 0 then l1 else l2 in
        simple_guard l)
    , (fun (l, _) ->
        let delta = if L.mem c1 l then 1 else 0 in
        let delta = delta - if L.mem c2 l then 1 else 0 in
        c := !c + delta;
        !c >= 0)
      (*FIXME*)
    , L.of_list [ c1; c2 ] )
  ;;

  let of_constr (c : clock Rtccsl.constr) : t =
    match c with
    | Precedence (c1, c2) -> prec c1 c2 true
    | Causality (c1, c2) -> prec c1 c2 false
    | Exclusion clocks ->
      let l = List.map L.of_list @@ ([] :: List.map (fun x -> [ x ]) clocks) in
      stateless l clocks
    | Coincidence clocks ->
      let l = List.map L.of_list [ clocks; [] ] in
      stateless l clocks
    | _ -> failwith "not implemented"
  ;;

  module Strategy = struct
    let first num_decision : strategy =
      fun guard ->
      List.find_map
        (fun (l, c) ->
          let* n = num_decision c in
          Some (l, n))
        guard
    ;;

    let bounded bound lin_cond =
      assert (I.subset bound (I.pinf N.zero));
      let choice = I.inter lin_cond bound in
      if I.is_empty choice then None else Some choice
    ;;

    let slow bound lin_cond =
      let* choice = bounded bound lin_cond in
      let* a, _ = I.destr choice in
      a
    ;;

    let fast bound lin_cond =
      let* choice = bounded bound lin_cond in
      let* _, b = I.destr choice in
      b
    ;;
  end

  let bisimulate s a1 a2 n =
    let _, trans, _ = a2 in
    let result =
      collect n (fun () ->
        let* sol = step s a1 in
        if trans sol then Some sol else None)
    in
    if List.length result = n then Ok result else Error result
  ;;

  (*
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
  let of_spec spec = List.fold_left sync empty (List.map of_constr spec)
end

module MakeSimpleDebug
    (C : sig
       include ID
       include Sexplib0.Sexpable.S with type t := t
     end)
    (N : Num) =
struct
  include MakeSimple (C) (N)
  open Sexplib0.Sexp_conv

  let sexp_of_label label = sexp_of_list C.sexp_of_t @@ L.elements label
  let sexp_of_solution = sexp_of_pair sexp_of_label N.sexp_of_t
  let sexp_of_trace trace = sexp_of_list sexp_of_solution trace
end

let%test_module _ =
  (module struct
    module A =
      MakeSimpleDebug
        (struct
          include String

          let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_string
          let t_of_sexp = Sexplib0.Sexp_conv.string_of_sexp
        end)
        (struct
          include ExpOrder.Make (Int)

          let zero = 0
          let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_int
          let t_of_sexp = Sexplib0.Sexp_conv.int_of_sexp
        end)

    open Rtccsl

    let%test _ =
      let empty1 = A.of_spec [ Coincidence [ "a"; "b" ]; Exclusion [ "a"; "b" ] ] in
      let empty2 = A.empty in
      let strat = A.Strategy.first @@ A.Strategy.slow (A.I.make 1 2) in
      let steps = 10 in
      let trace = A.bisimulate strat empty1 empty2 steps in
      match trace with
      | Ok l | Error l -> Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l;
      Result.is_ok trace
    ;;
  end)
;;
