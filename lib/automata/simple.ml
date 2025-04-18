open Prelude

module type ID = sig
  open Interface
  include OrderedType
  include Stringable with type t := t
  include Sexplib0.Sexpable.S with type t := t
end

module type Num = sig
  include Interval.Num
  include Interface.ExpOrder.S with type t := t
  include Interface.Stringable with type t := t

  val zero : t
  val neg : t -> t
  val ( - ) : t -> t -> t
end

module type S = sig
  type clock
  type param
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
  val of_constr : (clock, param, num) Rtccsl.constr -> t
  val of_spec : (clock, param, num) Rtccsl.specification -> t
  val gen_trace : strategy -> int -> t -> solution list
  val gen_trace_until : strategy -> int -> num -> t -> solution list

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

module Make (C : ID) (N : Num) = struct
  type clock = C.t
  type num = N.t
  type param = C.t

  module L = struct
    include Set.Make (C)

    let to_string label =
      match to_list label with
      | [] -> "∅"
      | l -> List.to_string C.to_string l
    ;;
  end

  module I = Interval.MakeDebug (N)
  module CMap = Map.Make (C)

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
  let noop_guard now = [ L.empty, I.pinf_strict now ]
  let noop_transition n (_, n') = N.compare n n' < 0
  let empty : t = noop_guard, noop_transition, L.empty

  let guard_to_string (label, cond) =
    Printf.sprintf "%s ? %s" (L.to_string label) (I.to_string cond)
  ;;

  let solution_to_string (label, cond) =
    Printf.sprintf "%s ! %s" (L.to_string label) (N.to_string cond)
  ;;

  let correctness_check clocks labels (l, n) =
    let proj = L.inter clocks l in
    List.exists (fun (l', cond) -> L.equal proj l' && I.contains cond n) labels
  ;;

  let step a n sol =
    let _, transition, _ = a in
    transition n sol
  ;;

  let accept_trace a n t =
    List.fold_left
      (fun n (l, n') ->
         match n with
         | Some n -> if step a n (l, n') then Some n' else None
         | None -> None)
      (Some n)
      t
  ;;

  let debug_g name g now =
    let variants = g now in
    let _ =
      Format.printf
        "%s variants %s\n"
        name
        (List.to_string ~sep:" | " guard_to_string variants)
    in
    variants
  ;;

  let next_step strat (a : t) now : solution option =
    let guards, _, _ = a in
    (* let _ = print_endline "------" in *)
    let possible = guards now in
    (* let _ =
      Printf.printf "--- Candidates ---\n";
      List.print
        (fun guard -> Printf.printf "* %s\n" (guard_to_string guard))
        (List.filter (fun (l, _) -> not (L.is_empty l)) possible)
    in *)
    if List.is_empty possible
    then None
    else (
      let possible_shifted =
        List.map
          (fun (l, c) ->
             let c = I.shift_by c (N.neg now) in
             l, c)
          possible
      in
      let* l, d = strat possible_shifted in
      let sol = l, N.(d + now) in
      (* let _ = Printf.printf "decision: %s\n" (solution_to_string sol) in *)
      if step a now sol then Some sol else None)
  ;;

  let gen_trace s n (a : t) : solution list =
    List.unfold_for
      (fun now ->
         let* l, now = next_step s a now in
         Some ((l, now), now))
      N.zero
      n
  ;;

  let gen_trace_until s n time (a : t) : solution list * bool =
    let trace, was_cut =
      List.unfold_for_while
        (fun now ->
           let* l, now = next_step s a now in
           Some ((l, now), now))
        N.zero
        n
        (fun (_, n) -> N.less n time)
    in
    trace, not was_cut
  ;;

  let sync (a1 : t) (a2 : t) : t =
    let g1, t1, c1 = a1 in
    let g2, t2, c2 = a2 in
    let c = L.union c1 c2 in
    let conf_surface = L.inter c1 c2 in
    let sat_solver l l' =
      if
        L.is_empty conf_surface
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
      (* let _ = Printf.printf "sync---\n" in *)
      let g1 = g1 now in
      (* let _ =
        Printf.printf "sync sol 1: %s\n" (Sexplib0.Sexp.to_string @@ sexp_of_guard g1)
      in *)
      let g2 = g2 now in
      (* let _ =
        Printf.printf "sync sol 2: %s\n" (Sexplib0.Sexp.to_string @@ sexp_of_guard g2)
      in *)
      let pot_solutions = List.cartesian g1 g2 in
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

  (** Logical-only guard function translates labels to guard of transition, adds generic [eta < eta'] condition on real-time.**)
  let lo_guard l now = List.map (fun l -> l, I.pinf_strict now) l

  let stateless labels =
    let g = lo_guard labels in
    g, fun _ _ -> true
  ;;

  let prec c1 c2 strict =
    let c = ref 0 in
    let l1 = List.map L.of_list (List.powerset [ c1; c2 ]) in
    let l2 =
      List.filter
        (fun x ->
           if strict then not (L.mem c2 x) else not ((not @@ L.mem c1 x) && L.mem c2 x))
        l1
    in
    let g now =
      let l = if !c = 0 then l2 else l1 in
      lo_guard l now
    in
    ( g
    , fun _ (l, _) ->
        let delta = if L.mem c1 l then 1 else 0 in
        let delta = delta - if L.mem c2 l then 1 else 0 in
        let _ = c := !c + delta in
        !c >= 0 )
  ;;

  let const_int_param = function
    | IntConst c -> c
    | IntVar _ -> failwith "const_int_param: the parameter has to be constant"
  ;;

  let const_time_param = function
    | TimeConst c -> c
    | TimeVar _ -> failwith "const_time_param: the parameter has to be constant"
  ;;

  let of_constr
        ?(int_unwrap = const_int_param)
        ?(time_unwrap = const_time_param)
        (constr : (clock, param, I.num) constr)
    : t
    =
    let label_list = List.map L.of_list in
    let g, t =
      match constr with
      | Precedence { cause; conseq } -> prec cause conseq true
      | Causality { cause; conseq } -> prec cause conseq false
      | Exclusion clocks ->
        let l = label_list @@ ([] :: List.map (fun x -> [ x ]) clocks) in
        stateless l
      | Coincidence clocks ->
        let l = label_list [ clocks; [] ] in
        stateless l
      | RTdelay { out = b; arg = a; delay = l, r } ->
        let l = time_unwrap l in
        let r = time_unwrap r in
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
        let t _ (l, n') =
          let _ = if L.mem a l then Queue.push n' queue in
          let _ = if L.mem b l then ignore @@ Queue.pop queue in
          true
        in
        g, t
      | CumulPeriodic { out; period; error = e1, e2; offset }
      | AbsPeriodic { out; period; error = e1, e2; offset } ->
        let period = time_unwrap period in
        let e1 = time_unwrap e1 in
        let e2 = time_unwrap e2 in
        let offset = time_unwrap offset in
        let e = I.(e1 =-= e2) in
        let last = ref None in
        let g now =
          let when_next, when_empty =
            match !last with
            | None -> I.shift_by e offset, I.(now <-> N.(offset + e2))
            | Some v -> I.shift_by e N.(period + v), I.(now <-> N.(v + period + e2))
          in
          let positive_int = I.pinf_strict now in
          [ L.of_list [ out ], I.inter positive_int when_next; L.empty, when_empty ]
        in
        let t _ (l, n') =
          let _ =
            if L.mem out l
            then (
              let update =
                match constr with
                | CumulPeriodic _ -> n'
                | AbsPeriodic _ ->
                  (match !last with
                   | None -> offset
                   | Some last -> N.(last + period))
                | _ -> failwith "unreachable"
              in
              last := Some update)
          in
          true
        in
        g, t
      | Sporadic { out = c; at_least; strict } ->
        let at_least = time_unwrap at_least in
        let last = ref None in
        let g now =
          match !last with
          | None -> [ L.of_list [ c ], I.pinf_strict now; L.empty, I.pinf_strict now ]
          | Some v ->
            let next_after = N.(at_least + v) in
            [ ( L.of_list [ c ]
              , if strict then I.pinf_strict next_after else I.pinf next_after )
            ; (L.empty, I.(now <-> next_after))
            ]
        in
        let t _ (l, n') =
          let _ = if L.mem c l then last := Some n' in
          true
        in
        g, t
      | Periodic { out; base; period } ->
        let period = int_unwrap period in
        let labels_eqp = label_list [ [ base; out ]; [] ] in
        let labels_lp = label_list [ [ base ]; [] ] in
        let c = ref 0 in
        let g now =
          let labels = if !c = period - 1 then labels_eqp else labels_lp in
          lo_guard labels now
        in
        let t _ (l, _) =
          let _ =
            if L.mem base l then c := !c + 1;
            if L.mem out l then c := 0
          in
          0 <= !c && !c < period
        in
        g, t
      | Sample { out; arg; base } ->
        let labels_latched =
          label_list [ []; [ arg ]; [ out; arg; base ]; [ out; base ] ]
        in
        let labels_unlatched = label_list [ []; [ arg ]; [ out; arg; base ]; [ base ] ] in
        let latched = ref false in
        let g now =
          if !latched then lo_guard labels_latched now else lo_guard labels_unlatched now
        in
        let t _ (l, _) =
          let _ = if L.mem arg l then latched := true in
          let _ = if L.mem base l then latched := false in
          true
        in
        g, t
      | Delay { out; arg; delay = d1, d2; base } ->
        let d1 = int_unwrap d1 in
        let d2 = int_unwrap d2 in
        let _ = assert (d1 <= d2) in
        let diff_base = Option.is_some base in
        let base = Option.value base ~default:arg in
        let q =
          ExpirationQueue.create (fun x ->
            match x + 1 with
            | x when x > d2 -> None
            | x -> Some x)
        in
        let labels_empty = [ []; [ arg ]; [ arg; base ]; [ base ] ] in
        let labels_ne_can = [ []; [ arg ]; [ arg; base ]; [ out; base ]; [ base ] ] in
        let labels_ne_must = [ [ out; base ]; [ out; arg; base ]; [] ] in
        let g now =
          let labels =
            match ExpirationQueue.peek q with
            | None when d1 = 0 && d2 = 0 && diff_base ->
              [ []; [ arg ]; [ out; arg; base ]; [ base ] ]
            | None when d1 = 0 && d2 = 0 -> [ []; [ out; arg ] ]
            | None when d1 = 0 ->
              [ []; [ arg ]; [ out; arg; base ]; [ base ]; [ arg; base ] ]
            | None -> labels_empty
            | Some x when x = d2 -> labels_ne_must
            | Some x when d1 <= x -> labels_ne_can
            | Some _ -> labels_empty
          in
          let labels = List.sort_uniq (List.compare C.compare) labels in
          let labels = label_list labels in
          lo_guard labels now
        in
        let t _ (l, _) =
          let _ =
            if L.mem arg l
            then (
              match ExpirationQueue.last q with
              | Some x when x = 0 -> ()
              | _ -> ExpirationQueue.push q 0)
          in
          let test2 =
            if L.mem out l
            then (
              match ExpirationQueue.pop q with
              | None -> false
              | Some x -> x >= d1)
            else true
          in
          let test3 =
            if L.mem base l then not (ExpirationQueue.expiration_step q) else true
          in
          test2 && test3
        in
        g, t
      | Minus { out; arg; except } ->
        let labels =
          []
          :: [ out; arg ]
          :: List.flat_cartesian [ [ arg ]; [] ] (List.powerset_nz except)
        in
        stateless (label_list labels)
      | Union { out; args } ->
        let labels = [] :: List.map (fun l -> out :: l) (List.powerset_nz args) in
        stateless (label_list labels)
      | Alternate { first = a; second = b } ->
        let phase = ref false in
        let g n =
          let labels =
            if not !phase
            then [ L.empty; L.of_list [ a ] ]
            else [ L.empty; L.of_list [ b ] ]
          in
          lo_guard labels n
        in
        let t _ (l, _) =
          let _ = if L.mem a l then phase := true else if L.mem b l then phase := false in
          true
        in
        g, t
      | Fastest { out; left = a; right = b } | Slowest { out; left = a; right = b } ->
        let count = ref 0 in
        let g n =
          let general_labels = [ []; [ a; b; out ] ] in
          let fastest_labels =
            general_labels
            @
            match !count with
            | x when x > 0 -> [ [ a; out ]; [ b ] ]
            | x when x = 0 -> [ [ a; out ]; [ b; out ] ]
            | x when x < 0 -> [ [ b; out ]; [ a ] ]
            | _ -> failwith "unreachable"
          in
          let slowest_labels =
            general_labels
            @
            match !count with
            | x when x > 0 -> [ [ a ]; [ b; out ] ]
            | x when x = 0 -> [ [ a ]; [ b ] ]
            | x when x < 0 -> [ [ b ]; [ a; out ] ]
            | _ -> failwith "unreachable"
          in
          let labels =
            match constr with
            | Fastest _ -> fastest_labels
            | Slowest _ -> slowest_labels
            | _ -> failwith "unreachable"
          in
          let labels = label_list labels in
          lo_guard labels n
        in
        let t _ (l, _) =
          let _ = if L.mem a l then count := !count + 1 in
          let _ = if L.mem b l then count := !count - 1 in
          true
        in
        g, t
      | Allow { from; until; args } | Forbid { from; until; args } ->
        let phase = ref false in
        let g_allow n =
          let labels =
            if !phase
            then
              List.flat_cartesian [ []; [ from; until ]; [ until ] ] (List.powerset args)
            else
              [] :: List.flat_cartesian [ [ from ]; [ from; until ] ] (List.powerset args)
          in
          let labels = label_list labels in
          lo_guard labels n
        in
        let g_forbid n =
          let labels =
            if !phase
            then
              []
              :: [ from ]
              :: List.flat_cartesian [ [ until ]; [ from; until ] ] (List.powerset args)
            else
              List.flat_cartesian
                [ []; [ from ]; [ from; until ]; [ until ] ]
                (List.powerset args)
          in
          let labels = label_list labels in
          lo_guard labels n
        in
        let g =
          match constr with
          | Allow _ -> g_allow
          | Forbid _ -> g_forbid
          | _ -> failwith "unreachable"
        in
        let t _ (l, _) =
          let from_test = L.mem from l in
          let until_test = L.mem until l in
          let _ =
            phase
            := match from_test, until_test with
               | true, true | false, false -> !phase
               | true, false -> true
               | false, true -> false
          in
          true
        in
        g, t
      | FirstSampled { out; arg; base } ->
        let sampled = ref false in
        let g n =
          let labels =
            if !sampled
            then [ []; [ arg ]; [ base ] ]
            else [ []; [ out; arg; base ]; [ out; arg ]; [ base ] ]
          in
          let labels = label_list labels in
          lo_guard labels n
        in
        let t _ (l, _) =
          let _ = if L.mem arg l then sampled := true in
          let _ = if L.mem base l then sampled := false in
          true
        in
        g, t
      | LastSampled { out; arg; base } ->
        let last = ref false in
        let g n =
          let labels =
            if !last
            then [ []; [ base ] ]
            else [ []; [ out; arg; base ]; [ out; arg ]; [ arg ] ]
          in
          lo_guard (label_list labels) n
        in
        let t _ (l, _) =
          let _ = if L.mem out l then last := true in
          let _ = if L.mem base l then last := false in
          true
        in
        g, t
      | Subclocking { sub = a; super = b } ->
        stateless (label_list [ []; [ a; b ]; [ b ] ])
      | Intersection { out; args } ->
        let labels = List.powerset args in
        let labels = List.map (fun l -> if l = args then out :: args else l) labels in
        stateless (label_list labels)
        (*FIXME: need evaluation of the expressions, just check if the assignment is inside the evaluated range*)
      | LogicalParameter _ | TimeParameter _ -> failwith "not implemented"
      | Pool (n, lock_unlocks) ->
        let locks, unlocks = List.split lock_unlocks in
        let lock_clocks, unlock_clocks = L.of_list locks, L.of_list unlocks in
        let _ = assert (L.is_empty (L.inter lock_clocks unlock_clocks)) in
        let injection_map list =
          List.fold_left
            (fun acc (from, into) ->
               CMap.update
                 from
                 (function
                   | Some _ -> failwith "not injective"
                   | None -> Some into)
                 acc)
            CMap.empty
            list
        in
        let locks_to_unlocks = injection_map lock_unlocks in
        let _ = injection_map (List.map Tuple.swap2 lock_unlocks) in
        let resources = ref [] in
        let g now =
          let free_now = n - List.length !resources in
          let to_free_variants = List.powerset (List.sort_uniq C.compare !resources) in
          to_free_variants
          |> List.to_seq
          |> Seq.flat_map (fun to_free ->
            let available = free_now + List.length to_free in
            List.powerset locks
            |> List.filter_map (fun l ->
              if List.length l > available then None else Some (to_free @ l))
            |> List.to_seq)
          |> Seq.map (fun l -> L.of_list l, I.pinf_strict now)
          |> List.of_seq
        in
        let t _ (l, _) =
          (* let _ = Printf.printf "---Transition---\n" in *)
          let to_lock = L.inter l lock_clocks in
          let to_unlock = L.inter l unlock_clocks in
          let new_resources =
            List.filter (fun unlock -> not( L.mem unlock to_unlock)) !resources
          in
          let new_resources =
            List.append
              new_resources
              (List.map (fun lock -> CMap.find lock locks_to_unlocks) (L.to_list to_lock))
          in
          let _ = resources := new_resources in
          (* let _ =
            Array.iter
              (fun x ->
                 match x with
                 | Some x -> Printf.printf "resource %s\n" (C.to_string x)
                 | None -> Printf.printf "not used\n")
              locks
          in *)
          true
        in
        g, t
    in
    g, t, L.of_list (clocks constr)
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

    let random_label ?(avoid_empty = false) attempts num_decision solutions =
      let solutions =
        if avoid_empty
        then List.filter (fun (l, _) -> not (L.is_empty l)) solutions
        else solutions
      in
      if List.is_empty solutions
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
      if I.is_empty choice then None else Some choice
    ;;

    let random_leap upper_bound up down rand cond =
      let left_bound = Option.value ~default:N.zero (I.left_bound_opt cond) in
      let cond =
        if I.is_right_unbound cond
        then I.inter cond I.(left_bound =-= N.(left_bound + upper_bound))
        else cond
      in
      let x, y =
        match cond with
        | I.Bound (I.Include x, I.Include y) -> x, y
        | I.Bound (I.Exclude x, I.Include y) -> up x y, y
        | I.Bound (I.Include x, I.Exclude y) -> x, down x y
        | I.Bound (I.Exclude x, I.Exclude y) -> up x y, down x y
        | _ -> invalid_arg "random on infinite interval is not supported"
      in
      Some (rand x y)
    ;;

    let slow upper_bound round_up cond =
      let left_bound = Option.value ~default:N.zero (I.left_bound_opt cond) in
      let cond = I.inter cond I.(left_bound =-= N.(left_bound + upper_bound)) in
      let v =
        match cond with
        | I.Bound (I.Include x, _) -> x
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
      List.unfold_for
        (fun now ->
           let* l, n = next_step s a1 now in
           if trans now (l, n) then Some ((l, n), n) else None)
        N.zero
        n
    in
    if List.length result = n then Ok result else Error result
  ;;

  let proj_trace clocks trace = List.map (fun (l, n) -> L.inter clocks l, n) trace
  let skip_empty trace = List.filter (fun (l, _) -> not (L.is_empty l)) trace

  let trace_to_svgbob ?(numbers = false) ?(tasks = []) ?precision clocks trace =
    if List.is_empty clocks
    then ""
    else (
      let clocks =
        clocks
        |> List.to_seq
        |> Seq.filter (fun c ->
          not
            (List.exists (fun (_, r, s, f, d) -> c = r || c = s || c = f || c = d) tasks))
        |> Array.of_seq
      in
      let clock_strs = Array.map C.to_string clocks in
      let len = Array.length clocks in
      let biggest_clock =
        clock_strs |> Array.to_seq |> Seq.map String.length |> Seq.fold_left Int.max 0
      in
      let biggest_task_name =
        tasks
        |> List.map (fun (name, _, _, _, _) -> String.length (C.to_string name))
        |> List.fold_left Int.max 0
      in
      let graph_prefix = Int.max biggest_task_name biggest_clock in
      let buffers =
        Array.init len (fun i ->
          let c = Array.get clock_strs i in
          let b = Buffer.create (graph_prefix + 32) in
          let symbol = if i = 0 then '+' else '|' in
          Printf.bprintf b "%*s %c-" graph_prefix c symbol;
          b)
      and footer = Buffer.create (graph_prefix + 32)
      and history = Buffer.create (graph_prefix + 32) in
      let _ =
        Buffer.add_chars footer graph_prefix ' ';
        Buffer.add_string footer " +-";
        Buffer.add_chars history (graph_prefix + 3) ' '
      in
      let clock_counters = Array.make len 0 in
      let counter i =
        let c = clock_counters.(i) in
        let _ = Array.set clock_counters i (c + 1) in
        c + 1
      in
      let marker i =
        if numbers
        then Int.to_string (counter i)
        else (
          match Int.rem i 6 with
          | 0 -> "*"
          | 1 -> "o"
          | 2 -> "◆"
          | 3 -> ">"
          | 4 -> "O"
          | 5 -> "^"
          | 6 -> "#"
          | _ -> failwith "unreachable")
      in
      let module TMap =
        Map.Make (struct
          type t = C.t * C.t * C.t * C.t

          let compare = Tuple.compare_same4 C.compare
        end)
      in
      let serialize_label task_state (l, n') =
        (* let delta = N.(n' - n) in *)
        let time_label = N.to_string n' in
        let time_label =
          match precision with
          | Some precision ->
            let dot_index = String.index time_label '.' in
            let right_bound =
              Int.min (String.length time_label) (dot_index + precision + 1)
            in
            String.sub time_label 0 right_bound
          | None -> time_label
        in
        let step_len = String.length time_label + 1 in
        let print_task ((name, r, s, f, d), (buf, executes)) =
          let ready = L.mem r l
          and start = L.mem s l
          and finish = L.mem f l
          and deadline = L.mem d l in
          let executes = (executes || start) && not finish in
          let symbol =
            match ready, deadline with
            | true, true -> "╳"
            | true, false -> "("
            | false, true -> ")"
            | false, false -> if start || finish || executes then "#" else "-"
          in
          Buffer.add_string buf symbol;
          if executes
          then Buffer.add_chars buf (step_len - 1) '#'
          else Buffer.add_chars buf (step_len - 1) '-';
          (name, r, s, f, d), (buf, executes)
        in
        let task_state = List.map print_task task_state in
        let print_clock placed i c =
          let buf = Array.get buffers i in
          let symbol, placed =
            if L.mem c l then marker i, true else if placed then "|", true else "-", false
          in
          Buffer.add_string buf symbol;
          Buffer.add_chars buf (step_len - String.grapheme_length symbol) '-';
          (*FIXME: numbers can have non-1 width, will crash when number is bigger than window length*)
          placed
        in
        let placed = Seq.fold_lefti print_clock false (Array.to_seq clocks) in
        Buffer.add_string footer (if placed then "┴" else "+");
        Buffer.add_chars footer (step_len - 1) '-';
        Printf.bprintf history "%s " time_label;
        task_state
      in
      let task_state =
        List.fold_left
          serialize_label
          (List.map (fun t -> t, (Buffer.create 32, false)) tasks)
          trace
      in
      let total = Buffer.create 1024 in
      let _ =
        List.iter
          (fun ((name, _, _, _, _), (buf, _)) ->
             Printf.bprintf total "%*s |-" graph_prefix (C.to_string name);
             Buffer.add_buffer total buf;
             Buffer.add_char total '\n';
             Buffer.add_chars total graph_prefix ' ';
             Buffer.add_string total " |\n")
          task_state;
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

  let trace_to_csl trace =
    let serialize (l, _) = List.to_string ~sep:"," C.to_string (L.to_list l) in
    List.to_string ~sep:",STEP," serialize trace
  ;;
end

let%test_module _ =
  (module struct
    open Rtccsl
    open Number
    module A = Make (Clock.String) (Float)

    let step = 0.1
    let slow_strat = A.Strategy.first @@ A.Strategy.slow 2.0 (Float.round_up step)

    let random_strat =
      A.Strategy.random_label
        1
        (A.Strategy.random_leap
           1.0
           (Float.round_up step)
           (Float.round_down step)
           Float.random)
    ;;

    let%test _ =
      let a = A.of_constr (Coincidence [ "a"; "b" ]) in
      not (List.is_empty (A.gen_trace slow_strat 10 a))
    ;;

    let%test _ =
      let a = A.of_constr (Coincidence [ "a"; "b" ]) in
      not (List.is_empty (A.gen_trace slow_strat 10 a))
    ;;

    let%test _ =
      let a = A.of_constr (Coincidence [ "a"; "b" ]) in
      let trace = A.gen_trace random_strat 10 a in
      not (List.is_empty trace)
    ;;

    let%test _ =
      let g, _, _ = A.of_constr (Coincidence [ "a"; "b" ]) in
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0); *)
      not (List.is_empty (g 0.0))
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
      let sampling1 =
        A.of_constr
        @@ Delay { out = "o"; arg = "i"; delay = IntConst 0, IntConst 0; base = Some "b" }
      in
      let sampling2 = A.of_constr @@ Sample { out = "o"; arg = "i"; base = "b" } in
      let steps = 10 in
      let trace = A.bisimulate random_strat sampling1 sampling2 steps in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Result.is_ok trace
    ;;

    let%test _ =
      let a = A.of_constr (Precedence { cause = "a"; conseq = "b" }) in
      let trace = A.gen_trace slow_strat 10 a in
      (* let g, _, _ = a in *)
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0);
      Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace trace; *)
      List.length trace = 10
    ;;
  end)
;;

module MakeExtendedString (N : Num) = struct
  include Make (Clock.String) (N)

  let trace_of_strings l =
    let to_clock_seq (c, s) =
      Seq.map (fun char -> if char = 'x' then Some c else None) (String.to_seq s)
    in
    let clock_traces = List.map to_clock_seq l in
    let clocks_trace = Seq.zip_list clock_traces in
    List.of_seq
    @@ Seq.map
         (fun cs ->
            let clocks, _ = List.flatten_opt cs in
            L.of_list clocks)
         clocks_trace
  ;;

  let trace_of_regexp str =
    let rec parse_single cs =
      let single_clocks, par, rest =
        Seq.fold_left_until
          (fun c -> c <> '(')
          (fun acc x ->
             let label = L.singleton (String.init_char 1 x) in
             acc @ [ label ])
          []
          cs
      in
      match par with
      | Some _ -> single_clocks @ parse_group rest
      | None -> single_clocks
    and parse_group cs =
      let label, par, rest =
        Seq.fold_left_until
          (fun c -> c <> ')')
          (fun acc x ->
             let c = String.init_char 1 x in
             acc @ [ c ])
          []
          cs
      in
      let label = L.of_list label in
      match par with
      | Some _ -> label :: parse_single rest
      | None -> [ label ]
    in
    parse_single (String.to_seq str)
  ;;

  let%test _ =
    trace_of_regexp "ab(cd)"
    = trace_of_strings [ "a", "x  "; "b", " x "; "c", "  x"; "d", "  x" ]
  ;;
end
