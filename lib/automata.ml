open Prelude

module type ID = sig
  include Set.OrderedType
  include Stringable with type t := t
  include Sexplib0.Sexpable.S with type t := t
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
    val slow : num_cond -> (num -> num -> num) -> num_cond -> num option
    val fast : num_cond -> (num -> num -> num) -> num_cond -> num option
    val random_label : int -> (num_cond -> num option) -> strategy

    val random_leap
      :  num_cond
      -> (num -> num -> num)
      -> (num -> num -> num)
      -> (num -> num -> num)
      -> num_cond
      -> num option
  end
end

module type Num = sig
  include Interval.Num
  include ExpOrder.T with type t := t

  val zero : t
  val neg : t -> t
  val ( - ) : t -> t -> t
  val t_to_string : t -> string
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

  open Sexplib0.Sexp_conv

  let sexp_of_label label = sexp_of_list C.sexp_of_t @@ L.elements label
  let sexp_of_solution = sexp_of_pair sexp_of_label N.sexp_of_t
  let sexp_of_trace trace = sexp_of_list sexp_of_solution trace
  let sexp_of_guard guard = sexp_of_list (sexp_of_pair sexp_of_label I.sexp_of_t) guard

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
      (* let _ =
        Printf.printf
          "pre-strat: now=%s sols=%s\n"
          (Sexplib0.Sexp.to_string @@ N.sexp_of_t now)
          (Sexplib0.Sexp.to_string @@ sexp_of_guard possible)
      in *)
      let* l, d = strat possible in
      let sol = l, N.(d + now) in
      (* let _ =
        Printf.printf
          "post-strat: sol=%s\n"
          (Sexplib0.Sexp.to_string @@ sexp_of_solution sol)
      in *)
      if transition now sol then Some sol else None)
  ;;

  let run s (a : t) n : solution list =
    collect n N.zero (fun now ->
      let* l, now = step s a now in
      Some ((l, now), now))
  ;;

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
      (* let _ =
        Printf.printf "sync sol 1: %s\n" (Sexplib0.Sexp.to_string @@ sexp_of_guard g1)
      in *)
      let g2 = g2 now in
      (* let _ =
        Printf.printf "sync sol 2: %s\n" (Sexplib0.Sexp.to_string @@ sexp_of_guard g2)
      in *)
      let pot_solutions = cartesian g1 g2 in
      let solutions = List.filter_map guard_solver pot_solutions in
      (* let _ =
        Printf.printf
          "sync sols: %s\n"
          (Sexplib0.Sexp.to_string @@ sexp_of_guard solutions)
      in *)
      solutions
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
          if strict then not (L.mem c2 x) else not ((not @@ L.mem c1 x) && L.mem c2 x))
        l1
    in
    let g now =
      let l = if !c = 0 then l2 else l1 in
      simple_guard l now
    in
    let clocks = L.of_list [ c1; c2 ] in
    ( g
    , (fun n (l, n') ->
        let test = correctness_check clocks (g n) (l, n') in
        let delta = if L.mem c1 l then 1 else 0 in
        let delta = delta - if L.mem c2 l then 1 else 0 in
        let _ = c := !c + delta in
        !c >= 0 && test)
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
        if Queue.is_empty queue
        then [ L.of_list [ a ], I.pinf_strict now; L.empty, I.pinf_strict now ]
        else (
          let head = Queue.peek queue in
          let next = I.inter (I.pinf_strict now) (I.shift_by delay head) in
          [ (L.of_list [ a ], I.(now <-> N.(head + l)))
          ; (L.empty, I.(now <-> N.(head + r)))
          ; L.of_list [ a; b ], next
          ; L.of_list [ b ], next
          ])
      in
      let clocks = L.of_list [ a; b ] in
      let t n (l, n') =
        let test = correctness_check clocks (g n) (l, n') in
        let _ = if L.mem a l then Queue.push n' queue in
        let _ = if L.mem b l then ignore @@ Queue.pop queue in
        (* let _ =
          Printf.printf "trans: test=%b sol=%s\n" test
          @@ Sexplib0.Sexp.to_string
          @@ sexp_of_solution (l, n')
        in *)
        test
      in
      g, t, clocks
    | CumulPeriodic (c, d, (e1, e2), off) | AbsPeriodic (c, d, (e1, e2), off) ->
      let e = I.(e1 =-= e2) in
      let _ = Printf.printf "%s\n" (Sexplib0.Sexp.to_string @@ I.sexp_of_t e) in
      let last = ref None in
      let g now =
        let next, right_bound =
          match !last with
          | None -> I.shift_by e off, N.(off + e2)
          | Some v -> I.shift_by e N.(d + v), N.(v + d + e2)
        in
        let generic = I.pinf_strict now in
        [ L.of_list [ c ], I.inter generic next; (L.empty, I.(N.zero <-> right_bound)) ]
      in
      let clocks = L.of_list [ c ] in
      let t n (l, n') =
        let test = correctness_check clocks (g n) (l, n') in
        let _ =
          if L.mem c l
          then (
            let update =
              match cons with
              | CumulPeriodic _ -> n'
              | AbsPeriodic _ ->
                (match !last with
                 | None -> off
                 | Some last -> N.(last + d))
              | _ -> failwith "unreachable"
            in
            (* let _ =
               Printf.printf
               "update := %s\n"
               (Sexplib0.Sexp.to_string (N.sexp_of_t update))
               in *)
            last := Some update)
        in
        test
      in
      g, t, clocks
    | Sporadic (c, d) ->
      let last = ref None in
      let g now =
        match !last with
        | None -> [ L.of_list [ c ], I.pinf_strict now; L.empty, I.pinf_strict now ]
        | Some v ->
          let next_after = N.(d + v) in
          [ L.of_list [ c ], I.pinf_strict next_after; (L.empty, I.(now <-> next_after)) ]
      in
      let clocks = L.of_list [ c ] in
      let t n (l, n') =
        let test = correctness_check clocks (g n) (l, n') in
        let _ = if L.mem c l then last := Some n' in
        test
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

    let random_label attempts num_decision solutions =
      if is_empty solutions
      then None
      else (
        let len = List.length solutions in
        let rand _ =
          let choice = Random.int len in
          let l, c = List.nth solutions choice in
          let* n = num_decision c in
          Some (l, n)
        in
        Seq.find_map (fun x -> x) (Seq.init attempts rand))
    ;;

    let bounded bound lin_cond =
      assert (I.subset bound (I.pinf N.zero));
      let choice = I.inter lin_cond bound in
      (* let _ =
         Printf.printf "bounded: %s\n" (Sexplib0.Sexp.to_string (I.sexp_of_t choice))
         in *)
      if I.is_empty choice then None else Some choice
    ;;

    let random_leap bound up down rand cond =
      let cond = I.inter cond bound in
      if I.is_empty cond
      then None
      else (
        let x, y =
          match cond with
          | I.Bound (I.Include x, I.Include y) -> x, y
          | I.Bound (I.Exclude x, I.Include y) -> up x y, y
          | I.Bound (I.Include x, I.Exclude y) -> x, down x y
          | I.Bound (I.Exclude x, I.Exclude y) -> up x y, down x y
          | _ -> invalid_arg "random on infinite interval is not supported"
        in
        Some (rand x y))
    ;;

    let slow bound round_up lin_cond =
      let* choice = bounded bound lin_cond in
      let v =
        match choice with
        | I.Bound (I.Include x, I.Include _) | I.Bound (I.Include x, I.Exclude _) -> x
        | I.Bound (I.Exclude x, I.Include y) | I.Bound (I.Exclude x, I.Exclude y) ->
          round_up x y
        | _ -> invalid_arg "random on infinite interval is not supported"
      in
      Some v
    ;;

    let fast bound round_down lin_cond =
      let* choice = bounded bound lin_cond in
      let v =
        match choice with
        | I.Bound (I.Include _, I.Include y) | I.Bound (I.Exclude _, I.Include y) -> y
        | I.Bound (I.Include x, I.Exclude y) | I.Bound (I.Exclude x, I.Exclude y) ->
          round_down x y
        | _ -> invalid_arg "random on infinite interval is not supported"
      in
      Some v
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

  (*TODO: add idices instead of dots for clocks*)
  let trace_to_svgbob clocks trace =
    if L.is_empty clocks
    then ""
    else (
      let clock_strs = Array.of_list (List.map C.t_to_string (L.elements clocks)) in
      let clocks = Array.of_list (L.elements clocks) in
      let len = Array.length clocks in
      let biggest_clock =
        Option.get
        @@ Seq.fold_left
             (fun biggest c ->
               match biggest with
               | None -> Some c
               | Some b -> Some (Int.max b c))
             None
             (Seq.map String.length (Array.to_seq clock_strs))
      in
      let graph_offset = biggest_clock + 3 in
      let buffers =
        Array.init len (fun i ->
          let c = Array.get clock_strs i in
          let b = Buffer.create (biggest_clock + 32) in
          let symbol = if i = 0 then '+' else '|' in
          Printf.bprintf b "%*s %c-" biggest_clock c symbol;
          b)
      and footer = Buffer.create (biggest_clock + 32)
      and history = Buffer.create (biggest_clock + 32) in
      let _ =
        Buffer.add_chars footer biggest_clock ' ';
        Buffer.add_string footer " +-";
        Buffer.add_chars history graph_offset ' '
      in
      let rec print _ = function
        | [] -> ()
        | (l, n') :: tail ->
          (* let delta = N.(n' - n) in *)
          let time_label = N.t_to_string n' in
          let len = String.length time_label + 1 in
          let print_clock mark i c =
            let buf = Array.get buffers i in
            let symbol, mark =
              if L.mem c l then '*', true else if mark then '|', true else '-', false
            in
            Buffer.add_char buf symbol;
            Buffer.add_chars buf (len - 1) '-';
            mark
          in
          let _ = Seq.fold_lefti print_clock false (Array.to_seq clocks) in
          let _ =
            Buffer.add_char footer '+';
            Buffer.add_chars footer (len - 1) '-';
            Printf.bprintf history "%s " time_label
          in
          print n' tail
      in
      let _ = print N.zero trace in
      let total_length =
        Array.fold_left
          (fun len b -> len + Buffer.length b)
          (Buffer.length footer + Buffer.length history + len + 32)
          buffers
      in
      let total = Buffer.create total_length in
      let _ =
        Array.iter
          (fun b ->
            Buffer.add_buffer total b;
            Buffer.add_char total '\n')
          buffers;
        Buffer.add_buffer total footer;
        Buffer.add_string total ">\n";
        Buffer.add_buffer total history;
        Buffer.add_string total "seconds"
      in
      Buffer.contents total)
  ;;
end

let%test_module _ =
  (module struct
    open Rtccsl
    open Number
    module A = MakeSimple (Clock.String) (Float)

    let step = 0.1

    let slow_strat =
      A.Strategy.first @@ A.Strategy.slow (A.I.make_include 1.0 2.0) (Float.round_up step)
    ;;

    let%test _ =
      let a = A.of_constr (Coincidence [ "a"; "b" ]) in
      not (is_empty (A.run slow_strat a 10))
    ;;

    let random_strat =
      A.Strategy.random_label
        1
        (A.Strategy.random_leap
           A.I.(0.0 =-= 1.0)
           (Float.round_up step)
           (Float.round_down step)
           Float.random)
    ;;

    let%test _ =
      let a = A.of_constr (Coincidence [ "a"; "b" ]) in
      not (is_empty (A.run slow_strat a 10))
    ;;

    let%test _ =
      let a = A.of_constr (Coincidence [ "a"; "b" ]) in
      let trace = A.run random_strat a 10 in
      not (is_empty trace)
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
      let trace = A.bisimulate slow_strat empty1 empty2 steps in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Result.is_ok trace
    ;;

    let%test _ =
      let a = A.of_constr (Precedence ("a", "b")) in
      let trace = A.run slow_strat a 10 in
      (* let g, _, _ = a in *)
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0);
      Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace trace; *)
      List.length trace = 10
    ;;
  end)
;;
