open Prelude

module type ID = sig
  include Set.OrderedType
end

module type Simple = sig
  type clock
  type num
  type label

  module I : Interval.I with type num = num
  module L : Set.S with type elt = clock

  type num_cond = I.t
  type guard = (label * num_cond) list
  type solution = label * num
  type strategy = guard -> solution option
  type trace = solution list
  type t = (num -> guard) * (num -> solution -> bool) * label

  val empty : t
  val step : strategy -> t -> num -> solution option
  val run : strategy -> t -> int -> trace
  val bisimulate : strategy -> t -> t -> int -> (trace, trace) result
  val sync : t -> t -> t
  val of_constr : (clock, num) Rtccsl.constr -> t
  val of_spec : (clock, num) Rtccsl.specification -> t

  module Strategy : sig
    val first : (num_cond -> num option) -> strategy
    val slow : num_cond -> (I.bound -> I.bound -> num) -> num_cond -> num option
    val fast : num_cond -> (I.bound -> I.bound -> num) -> num_cond -> num option
  end
end

module type Num = sig
  include Interval.Num
  include ExpOrder.T with type t := t

  val zero : t
  val neg : t -> t
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
  type t = (num -> guard) * (num -> solution -> bool) * label

  let empty : t =
    ( (fun now -> [ L.empty, I.pinf_strict now ])
    , (fun n (_, n') -> N.compare n n' < 0)
    , L.empty )
  ;;

  let step strat (a : t) now : solution option =
    let guards, transition, _ = a in
    let possible = guards now in
    if is_empty possible
    then None
    else (
      let possible =
        List.map
          (fun (l, c) ->
            let c = I.shift_by c (N.neg now) in
            l, c)
          possible
      in
      let* l, d = strat possible in
      let sol = l, N.(d + now) in
      if transition now sol then Some sol else None)
  ;;

  let run s (a : t) n : solution list =
    collect n N.zero (fun now ->
      let* l, now = step s a now in
      Some ((l, now), now))
  ;;

  (*TODO: add CSV output*)

  (*TODO: add visualization?*)

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
    let g now =
      let g1 = g1 now in
      let g2 = g2 now in
      List.filter_map guard_solver @@ cartesian g1 g2
    in
    let t n l = t1 n l && t2 n l in
    g, t, c
  ;;

  open Rtccsl

  let simple_guard l now = List.map (fun l -> l, I.pinf_strict now) l

  let correctness_check clocks labels (l, n) =
    let proj = L.inter clocks l in
    List.exists (fun (l', cond) -> L.equal proj l' && I.contains cond n) labels
  ;;

  let stateless labels clocks : t =
    let clocks = L.of_list clocks in
    let g = simple_guard labels in
    g, (fun n s -> correctness_check clocks (g n) s), clocks
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
    let g now =
      let l = if !c = 0 then l1 else l2 in
      simple_guard l now
    in
    let clocks = L.of_list [ c1; c2 ] in
    ( g
    , (fun n (l, n') ->
        let delta = if L.mem c1 l then 1 else 0 in
        let delta = delta - if L.mem c2 l then 1 else 0 in
        c := !c + delta;
        !c >= 0 && correctness_check clocks (g n) (l, n'))
    , clocks )
  ;;

  let of_constr (cons : (clock, I.num) Rtccsl.constr) : t =
    match cons with
    | Precedence (c1, c2) -> prec c1 c2 true
    | Causality (c1, c2) -> prec c1 c2 false
    | Exclusion clocks ->
      let l = List.map L.of_list @@ ([] :: List.map (fun x -> [ x ]) clocks) in
      stateless l clocks
    | Coincidence clocks ->
      let l = List.map L.of_list [ clocks; [] ] in
      stateless l clocks
    | RTdelay (a, b, (l, r)) ->
      let queue = Queue.create () in
      let delay = I.(l =-= r) in
      let g now =
        let basic_behav =
          [ L.of_list [ a ], I.pinf_strict now; L.empty, I.pinf_strict now ]
        in
        if Queue.is_empty queue
        then basic_behav
        else (
          let head = Queue.peek queue in
          let next = I.inter (I.pinf_strict now) (I.shift_by delay head) in
          List.append basic_behav [ L.of_list [ a; b ], next; L.of_list [ b ], next ])
      in
      let clocks = L.of_list [ a; b ] in
      let t n (l, n') =
        if L.mem a l then Queue.push n' queue;
        correctness_check clocks (g n) (l, n')
      in
      g, t, clocks
    | CumulPeriodic (c, d, (e1, e2), off) | AbsPeriodic (c, d, (e1, e2), off) ->
      let e = I.make_include e1 e2 in
      let last = ref None in
      let g now =
        let generic = I.pinf_strict now in
        let next =
          match !last with
          | None -> I.shift_by e off
          | Some v -> I.shift_by e N.(d + v)
        in
        [ L.of_list [ c ], I.inter generic next
        ; L.empty, I.inter generic (Option.get @@ I.complement_left next)
        ]
      in
      let clocks = L.of_list [ c ] in
      let t n (l, n') =
        if L.mem c l
        then (
          let update =
            match cons with
            | CumulPeriodic _ -> n'
            | AbsPeriodic _ -> N.(Option.value !last ~default:N.zero + d)
            | _ -> failwith "unreachable"
          in
          last := Some update);
        correctness_check clocks (g n) (l, n')
      in
      g, t, clocks
    | Sporadic (c, d) ->
      let last = ref None in
      let g now =
        match !last with
        | None -> [ L.of_list [ c ], I.pinf_strict now; L.empty, I.pinf_strict now ]
        | Some v ->
          let next_after = N.(d + v) in
          [ L.of_list [ c ], I.pinf next_after; (L.empty, I.(now <-> next_after)) ]
      in
      let clocks = L.of_list [ c ] in
      let t n (l, n') =
        if L.mem c l then last := Some n';
        correctness_check clocks (g n) (l, n')
      in
      g, t, clocks
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
       | FirstSampled (_, _, _) -> _
       | LastSampled (_, _, _) -> _
       | Forbid (_, _, _) -> _
       | Allow (_, _, _) -> _ *)
    | _ -> failwith "not implemented"
  ;;

  let of_spec spec = List.fold_left sync empty (List.map of_constr spec)

  module Strategy = struct
    let rec first num_decision = function
      | [] -> None
      | (l, c) :: tail ->
        if L.is_empty l
        then (
          match first num_decision tail with
          | None ->
            let* n = num_decision c in
            Some (l, n)
          | Some x -> Some x)
        else
          let* n = num_decision c in
          Some (l, n)
    ;;

    let bounded bound lin_cond =
      assert (I.subset bound (I.pinf N.zero));
      let choice = I.inter lin_cond bound in
      if I.is_empty choice then None else Some choice
    ;;

    let slow bound round_up lin_cond =
      let* choice = bounded bound lin_cond in
      let* a, b = I.destr choice in
      match a with
      | I.Include x -> Some x
      | I.Exclude _ -> Some (round_up a b)
      | Inf -> failwith "unreachable"
    ;;

    let fast bound round_down lin_cond =
      let* choice = bounded bound lin_cond in
      let* a, b = I.destr choice in
      match b with
      | I.Include x -> Some x
      | I.Exclude _ -> Some (round_down a b)
      | Inf -> failwith "unreachable"
    ;;
  end

  let bisimulate s a1 a2 n =
    let _, trans, _ = a2 in
    let result =
      collect n N.zero (fun now ->
        let* l, n = step s a1 now in
        if trans now (l, n) then Some ((l, n), n) else None)
    in
    if List.length result = n then Ok result else Error result
  ;;
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
  let sexp_of_guard guard = sexp_of_list (sexp_of_pair sexp_of_label I.sexp_of_t) guard
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
          include ExpOrder.Make (Float)

          let zero = Float.zero
          let ( + ) = Float.add
          let neg = Float.neg
          let sexp_of_t = Sexplib0.Sexp_conv.sexp_of_float
          let t_of_sexp = Sexplib0.Sexp_conv.float_of_sexp
        end)

    open Rtccsl

    let step = 0.1

    let round_up x y =
      Printf.printf "round_up";
      match x, y with
      | A.I.Include x, _ -> x
      | A.I.Exclude x, A.I.Include y | A.I.Exclude x, A.I.Exclude y ->
        let r = x +. step in
        if r < y then r else (x +. y) /. 2.
      | A.I.Exclude x, A.I.Inf -> x +. step
      | _ -> failwith "unreachable"
    ;;

    let strat = A.Strategy.first @@ A.Strategy.slow (A.I.make_include 1.0 2.0) round_up

    let%test _ =
      let a = A.of_constr (Coincidence [ "a"; "b" ]) in
      not (is_empty (A.run strat a 10))
    ;;

    let%test _ =
      let g, _, _ = A.of_constr (Coincidence [ "a"; "b" ]) in
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0); *)
      not (is_empty (g 0.0))
    ;;

    let%test _ =
      let empty1 = A.of_spec [ Coincidence [ "a"; "b" ]; Exclusion [ "a"; "b" ] ] in
      let empty2 = A.empty in
      let steps = 10 in
      let trace = A.bisimulate strat empty1 empty2 steps in
      match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l;
      Result.is_ok trace
    ;;
  end)
;;
