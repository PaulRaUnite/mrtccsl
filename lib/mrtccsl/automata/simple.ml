open Prelude

(**Type of distributions that can be used in a simulation. *)
type 'n distribution =
  | Uniform of
      { lower : 'n
      ; upper : 'n
      }
  | Normal of
      { mean : 'n
      ; dev : 'n
      }
[@@deriving map]

let truncated_guassian_rvs ~a ~b ~mu ~sigma =
  if Float.equal sigma 0.0
  then mu
  else (
    let prob_l, prob_r = Tuple.map2 (Owl.Stats.gaussian_cdf ~mu ~sigma) (a, b) in
    let sample_prob = Owl.Stats.uniform_rvs ~a:prob_l ~b:prob_r in
    Owl.Stats.gaussian_ppf sample_prob ~mu ~sigma)
;;

(**Specifies the distribution of the time variable. *)
type ('v, 't) dist_binding = 'v * 't distribution [@@deriving map]

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
  include Interface.OrderedType with type t := t

  val zero : t
  val one : t
  val neg : t -> t
  val ( - ) : t -> t -> t
  val random : t -> t -> t
  val to_float : t -> float
  val of_float : float -> t
end

module type Label = sig
  type t
  type elt

  val of_list : elt list -> t
  val singleton : elt -> t
  val mem : elt -> t -> bool
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val cardinal : t -> int
  val inter : t -> t -> t
  val to_seq : t -> elt Seq.t
  val of_seq : elt Seq.t -> t
  val is_empty : t -> bool
  val iter : (elt -> unit) -> t -> unit
  val to_iter : t -> (elt -> unit) -> unit
  val of_iter : ((elt -> unit) -> unit) -> t
end

module type Strategy = sig
  type var
  type num

  module I : Interval.I with type num := num
  module L : Label

  type guard = (L.t * I.t) Iter.t
  type solution = L.t * num

  module Var : sig
    type t = var -> I.t -> I.t

    val none : t
    val use_dist : (var, num) dist_binding list -> t
  end

  module Num : sig
    type t = I.t -> num

    val random_leap
      :  upper_bound:num
      -> ceil:(num -> num -> num)
      -> floor:(num -> num -> num)
      -> rand:(num -> num -> num)
      -> t

    val slow : upper_bound:num -> ceil:(num -> num -> num) -> t
    val fast : upper_bound:num -> floor:(num -> num -> num) -> t
  end

  module Solution : sig
    type t = guard -> solution option

    val first : Num.t -> t
    val random_label : Num.t -> t
    val avoid_empty : t -> t
    val refuse_empty : t -> t
  end
end

module type Trace = sig
  type t
  type solution
  type num

  val persist : ?size_hint:int -> t -> t
  val to_iter : t -> solution Iter.t
  val to_seq : t -> solution Seq.t
  val of_seq : solution Seq.t -> t
  val is_empty : t -> bool
  val until : horizon:num -> t -> t * bool ref
  val take : steps:int -> t -> t
end

module type S = sig
  module C : ID

  type clock = C.t
  type param = C.t
  type var = C.t

  module N : Num
  module I : Interval.I with type num = N.t
  module L : Label with type elt := clock

  type guard = (L.t * I.t) Iter.t
  type solution = L.t * N.t
  type var_strategy = var -> I.t -> I.t
  type sol_strategy = guard -> solution option

  type vars =
    { current : var -> I.t
    ; consume : var -> unit
    }

  type t = (vars -> N.t -> guard) * (vars -> N.t -> solution -> bool) * L.t
  type limits = var -> I.t
  type sim

  module Trace : Trace with type solution := solution and type num := N.t

  val empty_sim : sim
  val of_spec : (clock, param, var, N.t) Rtccsl.specification -> sim
  val gen_trace : var_strategy -> sol_strategy -> sim -> Trace.t
  val bisimulate : var_strategy -> sol_strategy -> sim -> sim -> Trace.t
  val accept_trace : sim -> N.t -> Trace.t -> N.t option
end

module MakeWithBijection
    (C : ID)
    (N : Num)
    (B : BitvectorSet.BijectionToInt.S with type elt = C.t) =
struct
  module C = C

  type clock = C.t
  type param = C.t
  type var = C.t

  module N = N

  module L = struct
    include BitvectorSet.Make (B)

    let to_string label =
      if is_empty label then "∅" else Iter.to_string ~sep:"," C.to_string (to_iter label)
    ;;
  end

  module I = Interval.MakeDebug (N)
  module CMap = Map.Make (C)

  type label = L.t
  type num_cond = I.t
  type guard = (label * num_cond) Iter.t
  type solution = label * N.t
  type var_strategy = var -> I.t -> I.t
  type sol_strategy = guard -> solution option

  module Trace = struct
    type t = solution Iter.t

    let persist ?size_hint t = t |> Iter.to_dynarray ?size_hint |> Iter.of_dynarray
    let of_seq t = t |> Iter.of_seq
    let to_iter = Fun.id
    let to_seq seq = Iter.to_seq_persistent seq
    let is_empty t = Iter.is_empty t

    let until ~horizon trace =
      let was_cut = ref false in
      ( Iter.take_while
          (fun [@inline hint] (_, n) ->
             if N.less n horizon
             then true
             else (
               was_cut := true;
               false))
          trace
      , was_cut )
    ;;

    let take ~steps = Iter.take steps
  end

  type vars =
    { current : var -> I.t
      (**[current v] returns current range of variable [v]. Raises [Not_found] if not present. *)
    ; consume : var -> unit (**[consume v] invalidates the value *)
    }

  type t = (vars -> N.t -> guard) * (vars -> N.t -> solution -> bool) * L.t
  type limits = var -> I.t

  type sim =
    { limits : limits
    ; automata : t
    }

  open Sexplib0.Sexp_conv

  let sexp_of_label label = sexp_of_list C.sexp_of_t @@ L.elements label
  let sexp_of_solution = sexp_of_pair sexp_of_label N.sexp_of_t
  let sexp_of_trace trace = sexp_of_list sexp_of_solution trace
  let sexp_of_guard guard = sexp_of_list (sexp_of_pair sexp_of_label I.sexp_of_t) guard

  let noop_guard _ now =
    Iter.of_array [| L.empty, I.inter (I.pinf N.zero) (I.pinf_strict now) |]
  ;;

  let noop_transition _ n (_, n') = N.compare n n' < 0
  let empty : t = noop_guard, noop_transition, L.empty

  let empty_sim : sim =
    { limits = (fun _ -> failwith "not implemented")
    ; automata = noop_guard, noop_transition, L.empty
    }
  ;;

  let variant_to_string (label, cond) =
    Printf.sprintf "%s ? %s" (L.to_string label) (I.to_string cond)
  ;;

  let guard_to_string variants = Iter.to_string ~sep:" || " variant_to_string variants

  let solution_to_string (label, now) =
    Printf.sprintf "%s ! %s" (L.to_string label) (N.to_string now)
  ;;

  let correctness_decorator a =
    let g, t, clocks = a in
    let t vars n (l, n') =
      let possible = g vars n in
      let present =
        Iter.exists
          (fun (l', cond) -> L.equal_modulo ~modulo:clocks l l' && I.contains cond n')
          possible
      in
      present && t vars n (l, n')
    in
    g, t, clocks
  ;;

  let debug_g name g vars now =
    let variants = g vars now in
    let _ = Printf.printf "<%s>: %s\n" name (guard_to_string variants) in
    variants
  ;;

  let sync (a1 : t) (a2 : t) : t =
    let g1, t1, c1 = a1 in
    let g2, t2, c2 = a2 in
    let c = L.union c1 c2 in
    let conf_surface = L.inter c1 c2 in
    let[@inline always] sat_solver l l' =
      if L.equal_modulo ~modulo:conf_surface l l' then Some (L.union l l') else None
    in
    let[@inline always] linear_solver c c' =
      let res = I.inter (I.pinf N.zero) (I.inter c c') in
      if I.is_empty res then None else Some res
    in
    let[@inline always] guard_solver ((l, c), (l', c')) =
      match sat_solver l l', linear_solver c c' with
      | Some l, Some c -> Some (l, c)
      | _ -> None
    in
    let g vars now =
      (* let _ = Printf.printf "sync--- at %s\n" (N.to_string now) in *)
      let g1 = g1 vars now
      (* let _ = Printf.printf "sync sol 1: %s\n" (guard_to_string g1) in *)
      and g2 = g2 vars now in
      (* let _ = Printf.printf "sync sol 2: %s\n" (guard_to_string g2) in *)
      let pot_solutions = Iter.product g1 g2 in
      let solutions = Iter.filter_map guard_solver pot_solutions in
      (* let _ = Printf.printf "sync sols: %s\n" (guard_to_string solutions) in *)
      Trace.persist solutions
    in
    let t vars n l = t1 vars n l && t2 vars n l in
    g, t, c
  ;;

  (** Logical-only guard function translates labels to guard of transition, adds generic [eta < eta'] condition on real-time.**)
  let lo_guard l =
    let l = Array.map (fun l -> l, I.pinf N.zero) l in
    fun _ _ -> l
  ;;

  let stateless labels =
    let g = lo_guard labels in
    g, fun _ _ _ -> true
  ;;

  let prec c1 c2 strict =
    let c = ref 0 in
    let l1 = List.map L.of_list (List.powerset [ c1; c2 ]) in
    let l2 =
      l1
      |> List.filter (fun x ->
        if strict then not (L.mem c2 x) else not ((not @@ L.mem c1 x) && L.mem c2 x))
      |> Array.of_list
    in
    let l1 = Array.of_list l1 in
    let g now =
      let l = if !c = 0 then l2 else l1 in
      lo_guard l now
    in
    ( g
    , fun _ _ (l, _) ->
        let delta = if L.mem c1 l then 1 else 0 in
        let delta = delta - if L.mem c2 l then 1 else 0 in
        let _ = c := !c + delta in
        !c >= 0 )
  ;;

  let of_constr constr : t =
    let open Rtccsl in
    let label_array l = Array.map L.of_list (Array.of_list l) in
    let g, t =
      match constr with
      | Precedence { cause; conseq } -> prec cause conseq true
      | Causality { cause; conseq } -> prec cause conseq false
      | Exclusion clocks ->
        let l = label_array ([] :: List.map (fun x -> [ x ]) clocks) in
        stateless l
      | Coincidence clocks ->
        let l = label_array [ clocks; [] ] in
        stateless l
      | RTdelay { out = b; arg = a; delay } ->
        let module Heap =
          Heap (struct
            include I

            let compare n n' =
              N.compare
                (Option.get @@ I.left_bound_opt n)
                (Option.get @@ I.left_bound_opt n')
            ;;
          end)
        in
        let queue = Heap.create () in
        let g _ now =
          match Heap.peek queue with
          | None -> [| L.singleton a, I.pinf_strict now; L.empty, I.pinf_strict now |]
          | Some next ->
            [| L.singleton a, Option.get (I.complement_left next)
             ; L.empty, Option.get (I.complement_left next)
             ; L.doubleton a b, next
             ; L.singleton b, next
            |]
        in
        let t vars _ (l, n') =
          let _ =
            if L.mem a l
            then (
              let v = vars.current delay in
              Heap.add queue (I.shift_by v n');
              vars.consume delay)
          in
          let _ = if L.mem b l then ignore (Heap.pop_min queue) in
          true
        in
        g, t
      | CumulPeriodic { out; period; offset = Const offset } ->
        let last = ref None in
        let g vars _ =
          let next =
            match !last with
            | None -> I.return offset
            | Some v -> I.shift_by (vars.current period) v
          in
          let g =
            [| L.singleton out, next; L.empty, Option.get (I.complement_left next) |]
          in
          (* let _ = Printf.printf "%s: %s\n" (C.to_string period) (guard_to_string g) in  *)
          g
        in
        let t vars _ (l, n') =
          let _ =
            if L.mem out l
            then (
              vars.consume period;
              last := Some n')
          in
          true
        in
        g, t
      | AbsPeriodic { out; period = Const period; error; offset = Const offset } ->
        let last = ref None in
        let g vars _ =
          let next =
            match !last with
            | None -> offset
            | Some v -> N.(v + period)
          in
          let next = I.shift_by (vars.current error) next in
          [| L.singleton out, next; L.empty, Option.get (I.complement_left next) |]
        in
        let t vars _ (l, _) =
          let _ =
            if L.mem out l
            then (
              let update =
                match !last with
                | None -> offset
                | Some last -> N.(last + period)
              in
              last := Some update;
              vars.consume error)
          in
          true
        in
        g, t
      | Sporadic { out = c; at_least = Const at_least; strict } ->
        let last = ref None in
        let g _ now =
          match !last with
          | None -> [| L.singleton c, I.pinf_strict now; L.empty, I.pinf_strict now |]
          | Some v ->
            let next_after = N.(at_least + v) in
            [| ( L.singleton c
               , if strict then I.pinf_strict next_after else I.pinf next_after )
             ; (L.empty, I.(now <-> next_after))
            |]
        in
        let t _ _ (l, n') =
          let _ = if L.mem c l then last := Some n' in
          true
        in
        g, t
      | Periodic { out; base; period = Const period } ->
        let labels_eqp = label_array [ [ base; out ]; [] ] in
        let labels_lp = label_array [ [ base ]; [] ] in
        let c = ref 0 in
        let g now =
          let labels = if !c = period - 1 then labels_eqp else labels_lp in
          lo_guard labels now
        in
        let t _ _ (l, _) =
          let _ =
            if L.mem base l then c := !c + 1;
            if L.mem out l then c := 0
          in
          0 <= !c && !c < period
        in
        g, t
      | Sample { out; arg; base } ->
        let labels_latched =
          label_array [ []; [ arg ]; [ out; arg; base ]; [ out; base ] ]
        in
        let labels_unlatched =
          label_array [ []; [ arg ]; [ out; arg; base ]; [ base ] ]
        in
        let latched = ref false in
        let g now =
          if !latched then lo_guard labels_latched now else lo_guard labels_unlatched now
        in
        let t _ _ (l, _) =
          let _ = if L.mem arg l then latched := true in
          let _ = if L.mem base l then latched := false in
          true
        in
        g, t
      | Delay { out; arg; delay = Const d1, Const d2; base } ->
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
          let labels = label_array labels in
          lo_guard labels now
        in
        let t _ _ (l, _) =
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
        stateless (label_array labels)
      | Union { out; args } ->
        let labels = [] :: List.map (fun l -> out :: l) (List.powerset_nz args) in
        stateless (label_array labels)
      | Alternate { first = a; second = b } ->
        let phase = ref false in
        let g n =
          let labels =
            if not !phase
            then [| L.empty; L.singleton a |]
            else [| L.empty; L.singleton b |]
          in
          lo_guard labels n
        in
        let t _ _ (l, _) =
          let _ = if L.mem a l then phase := true else if L.mem b l then phase := false in
          true
        in
        g, t
      | Fastest { out; left = a; right = b } | Slowest { out; left = a; right = b } ->
        let count = ref 0 in
        let general_labels = [ []; [ a; b; out ] ] in
        let g n =
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
          let labels = label_array labels in
          lo_guard labels n
        in
        let t _ _ (l, _) =
          let _ = if L.mem a l then count := !count + 1 in
          let _ = if L.mem b l then count := !count - 1 in
          true
        in
        g, t
      | Allow { from; until; args } | Forbid { from; until; args } ->
        let phase = ref false in
        let allow_l1 =
          label_array
          @@ List.flat_cartesian [ []; [ from; until ]; [ until ] ] (List.powerset args)
        and allow_l2 =
          label_array
          @@ ([] :: List.flat_cartesian [ [ from ]; [ from; until ] ] (List.powerset args))
        in
        let g_allow n =
          let labels = if !phase then allow_l1 else allow_l2 in
          lo_guard labels n
        in
        let forbid_l1 =
          label_array
          @@ ([]
              :: [ from ]
              :: List.flat_cartesian [ [ until ]; [ from; until ] ] (List.powerset args))
        and forbid_l2 =
          label_array
          @@ List.flat_cartesian
               [ []; [ from ]; [ from; until ]; [ until ] ]
               (List.powerset args)
        in
        let g_forbid n =
          let labels = if !phase then forbid_l1 else forbid_l2 in
          lo_guard labels n
        in
        let g =
          match constr with
          | Allow _ -> g_allow
          | Forbid _ -> g_forbid
          | _ -> failwith "unreachable"
        in
        let t _ _ (l, _) =
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
          let labels = label_array labels in
          lo_guard labels n
        in
        let t _ _ (l, _) =
          let _ = if L.mem arg l then sampled := true in
          let _ = if L.mem base l then sampled := false in
          true
        in
        g, t
      | LastSampled { out; arg; base } ->
        let last = ref false in
        let g vars n =
          let labels =
            if !last
            then [ []; [ base ] ]
            else [ []; [ out; arg; base ]; [ out; arg ]; [ arg ] ]
          in
          lo_guard (label_array labels) vars n
        in
        let t _ _ (l, _) =
          let _ = if L.mem out l then last := true in
          let _ = if L.mem base l then last := false in
          true
        in
        g, t
      | Subclocking { sub = a; super = b } ->
        stateless (label_array [ []; [ a; b ]; [ b ] ])
      | Intersection { out; args } ->
        let labels = List.powerset args in
        let labels = List.map (fun l -> if l = args then out :: args else l) labels in
        stateless (label_array labels)
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
        let g _ now =
          let free_now = n - List.length !resources in
          let to_free_variants = List.powerset (List.sort_uniq C.compare !resources) in
          to_free_variants
          |> Iter.of_list
          |> Iter.flat_map (fun to_free ->
            let available = free_now + List.length to_free in
            List.powerset locks
            |> Iter.of_list
            |> Iter.filter_map (fun l ->
              if List.length l > available then None else Some (to_free @ l)))
          |> Iter.map (fun l -> L.of_list l, I.pinf_strict now)
          |> Iter.to_dynarray
          |> Dynarray.to_array
        in
        let t _ _ (l, _) =
          (* let _ = Printf.printf "---Transition---\n" in *)
          let to_lock = L.inter l lock_clocks in
          let to_unlock = L.inter l unlock_clocks in
          let new_resources =
            List.filter (fun unlock -> not (L.mem unlock to_unlock)) !resources
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
      | _ -> failwith "not implemented"
    in
    let g vars now = Iter.of_array (g vars now) in
    let clocks = L.of_list (clocks constr) in
    correctness_decorator (g, t, clocks)
  ;;

  let of_var_rel =
    let open Rtccsl in
    function
    | TimeVarRelation (v, rel, Const c) ->
      let cond_f =
        match rel with
        | Less -> I.ninf_strict
        | LessEq -> I.ninf
        | More -> I.pinf_strict
        | MoreEq -> I.pinf
        | Eq -> I.return
        | Neq -> failwith "irrepresentable in interval domain"
      in
      let cond = cond_f c in
      CMap.singleton v cond
    | _ -> failwith "not implemented"
  ;;

  let of_spec spec : sim =
    let constraints =
      List.fold_left sync empty (List.map of_constr Rtccsl.(spec.constraints))
    and relations =
      spec.var_relations
      |> List.map of_var_rel
      |> List.fold_left (CMap.union (fun _ x y -> Some (I.inter x y))) CMap.empty
    in
    { limits = (fun v -> Option.value ~default:I.inf (CMap.find_opt v relations))
    ; automata = constraints
    }
  ;;

  let next_step strat (a : t) vars now : solution option =
    let guards, transition, _ = a in
    (* let _ = print_endline "------" in *)
    let possible = guards vars now in
    (* let _ =
      Printf.printf "--- Candidates ---\n";
      List.print
        (fun guard -> Printf.printf "* %s\n" (guard_to_string guard))
        (List.filter (fun (l, _) -> not (L.is_empty l)) possible)
    in *)
    if Iter.is_empty possible
    then None
    else
      let* sol = strat possible in
      (* let _ = Printf.printf "decision: %s\n" (solution_to_string sol) in *)
      if transition vars now sol then Some sol else None
  ;;

  let empty_vars = { current = (fun _ -> failwith "none"); consume = (fun _ -> ()) }

  let vars_from_rels (strat : var_strategy) (var2cond : var -> I.t) =
    let storage = ref CMap.empty in
    { current =
        (fun k ->
          match CMap.find_opt k !storage with
          | Some x -> x
          | None ->
            let new_v = strat k (var2cond k) in
            storage := CMap.add k new_v !storage;
            (* Printf.printf "generate %s with %s\n" (C.to_string k) (I.to_string new_v); *)
            new_v)
    ; consume =
        (fun k ->
          (* Printf.printf "consume %s\n" (C.to_string k); *)
          storage := CMap.remove k !storage)
    }
  ;;

  (*TODO: replace with iterator? Add dynarray.of_iter with size hint *)
  let gen_trace var_strat (sol_strat : sol_strategy) { limits; automata } : Trace.t =
    Iter.unfoldr
      (fun (vars, now) ->
         let* l, now = next_step sol_strat automata vars now in
         Some ((l, now), (vars, now)))
      (vars_from_rels var_strat limits, N.neg N.one)
  ;;

  let bisimulate var_strat s { limits; automata = a1; _ } { automata = a2; _ } =
    let _, trans, _ = a2 in
    Iter.unfoldr
      (fun (vars, now) ->
         let* l, n = next_step s a1 vars now in
         if trans vars now (l, n) then Some ((l, n), (vars, n)) else None)
      (vars_from_rels var_strat limits, N.zero)
  ;;

  (*TODO: investigate relation between the vrel1 and vrel2. *)

  let accept_trace { limits; automata; _ } n t =
    let step a vars n sol =
      let _, transition, _ = a in
      transition vars n sol
    in
    let _, result =
      Iter.fold
        (fun (vars, n) (l, n') ->
           match n with
           | Some n -> if step automata vars n (l, n') then vars, Some n' else vars, None
           | None -> vars, None)
        (vars_from_rels (fun _ c -> c) limits, Some n)
        t
    in
    result
  ;;

  let proj_trace clocks trace = Iter.map (fun (l, n) -> L.inter clocks l, n) trace
  let skip_empty trace = Iter.filter (fun (l, _) -> not (L.is_empty l)) trace
end

module Strategy (A : S) = struct
  open A
  module CMap = Map.Make (A.C)

  type var = A.var
  type num = A.N.t

  module L = A.L
  module I = A.I

  type guard = A.guard
  type solution = A.solution

  module Var = struct
    type t = var -> I.t -> I.t

    let none _ x = x

    let use_dist dist =
      let prepare (var, dist) =
        ( var
        , match dist with
          | Uniform { lower; upper } ->
            fun cond ->
              assert (I.subset I.(lower =-= upper) cond);
              I.return @@ N.random lower upper
          (* | AnyUniform -> N.random left right *)
          | Normal { mean; dev } ->
            let mu = N.to_float mean in
            let sigma = N.to_float dev in
            fun cond ->
              let bounds = Option.get @@ I.constant_bounds cond in
              let a, b = Tuple.map2 N.to_float bounds in
              let sample = truncated_guassian_rvs ~a ~b ~mu ~sigma in
              I.return @@ N.of_float sample )
      in
      let dist = dist |> List.map prepare |> CMap.of_list in
      fun var cond ->
        match CMap.find_opt var dist with
        | Some f -> f cond
        | None -> cond
    ;;
  end

  module Num = struct
    type t = I.t -> N.t

    let bounded bound lin_cond =
      assert (I.subset bound (I.pinf N.zero));
      let choice = I.inter lin_cond bound in
      if I.is_empty choice then None else Some choice
    ;;

    let random_leap ~upper_bound ~ceil ~floor ~rand cond =
      let left_bound = Option.value ~default:N.zero (I.left_bound_opt cond) in
      let cond =
        if I.is_right_unbound cond
        then I.inter cond I.(left_bound =-= N.(left_bound + upper_bound))
        else cond
      in
      let x, y =
        match cond with
        | I.Bound (I.Include x, I.Include y) -> x, y
        | I.Bound (I.Exclude x, I.Include y) -> ceil x y, y
        | I.Bound (I.Include x, I.Exclude y) -> x, floor x y
        | I.Bound (I.Exclude x, I.Exclude y) -> ceil x y, floor x y
        | _ -> invalid_arg "random on infinite interval is not supported"
      in
      rand x y
    ;;

    let slow ~upper_bound ~ceil cond =
      let left_bound = Option.value ~default:N.zero (I.left_bound_opt cond) in
      let cond = I.inter cond I.(left_bound =-= N.(left_bound + upper_bound)) in
      match cond with
      | I.Bound (I.Include x, _) -> x
      | I.Bound (I.Exclude x, I.Include y) | I.Bound (I.Exclude x, I.Exclude y) ->
        ceil x y
      | _ -> invalid_arg "random on infinite interval is not supported"
    ;;

    let fast ~upper_bound ~floor cond =
      let left_bound = Option.value ~default:N.zero (I.left_bound_opt cond) in
      let cond = I.inter cond I.(left_bound =-= N.(left_bound + upper_bound)) in
      match cond with
      | I.Bound (I.Include _, I.Include y) | I.Bound (I.Exclude _, I.Include y) -> y
      | I.Bound (I.Include x, I.Exclude y) | I.Bound (I.Exclude x, I.Exclude y) ->
        floor x y
      | _ -> invalid_arg "random on infinite interval is not supported"
    ;;
  end

  module Solution = struct
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
end

module Hashed = struct
  module type ID = sig
    include ID
    include Hashtbl.HashedType with type t := t
  end

  module BijectionLevel (C : ID) (N : Num) = struct
    include MakeWithBijection (C) (N) (BitvectorSet.BijectionToInt.Hashed (C))
  end

  module WithSession (C : ID) (N : Num) = struct
    module Inner =
      MakeWithBijection (Number.Integer) (N) (BitvectorSet.BijectionToInt.Int)

    module Session = struct
      module H = Hashtbl.Make (C)

      type t = int H.t * C.t Dynarray.t

      let create () =
        let mapping : int H.t = H.create 128 in
        let inverse : C.t Dynarray.t = Dynarray.create () in
        mapping, inverse
      ;;

      let to_offset (mapping, _) k = H.find mapping k
      let of_offset (_, inverse) i = Dynarray.get inverse i

      let save (mapping, inverse) k =
        match H.find_opt mapping k with
        | Some x -> x
        | None ->
          let x = Dynarray.length inverse in
          H.add mapping k x;
          Dynarray.add_last inverse k;
          x
      ;;

      let with_spec session spec =
        let f k = save session k in
        Rtccsl.map_specification f f f Fun.id spec
      ;;

      let with_dist session dist =
        let f = save session in
        map_dist_binding f Fun.id dist
      ;;
    end

    module L = struct
      let to_iter s l = l |> Inner.L.to_iter |> Iter.map (Session.of_offset s)
      let to_seq s l = l |> Inner.L.to_seq |> Seq.map (Session.of_offset s)
    end

    module Trace = struct
      let to_iter s t =
        t |> Inner.Trace.to_iter |> Iter.map (fun (l, n) -> L.to_iter s l, n)
      ;;

      let to_seq s t = t |> Inner.Trace.to_seq |> Seq.map (fun (l, n) -> L.to_seq s l, n)
    end
  end
end

module Make = Hashed.BijectionLevel
module Trace () = struct end

module Export = struct
  (* module type S = sig
    type trace
    type clock

    val trace_to_svgbob
      :  ?numbers:bool
      -> ?tasks:(clock * clock * clock * clock * clock) list
      -> ?precision:int
      -> clock list
      -> trace
      -> string

    val trace_to_vertical_svgbob
      :  ?numbers:bool
      -> ?tasks:(clock * clock * clock * clock * clock) list
      -> clock list
      -> out_channel
      -> trace
      -> unit

    val trace_to_csl : trace -> string
  end *)

  module Make
      (C : sig
         include Interface.Stringable
         include Interface.OrderedType with type t := t
       end)
      (N : Num)
      (L : sig
             type t
             type elt

             val mem : elt -> t -> bool
             val to_iter : t -> (elt -> unit) -> unit
           end
           with type elt = C.t) =
  struct
    let trace_to_svgbob ?(numbers = false) ?precision ~tasks clocks formatter trace =
      if List.is_empty clocks
      then ()
      else (
        let clocks =
          clocks
          |> List.to_seq
          |> Seq.filter (fun c ->
            not
              (List.exists
                 (fun (_, r, s, f, d) -> c = r || c = s || c = f || c = d)
                 tasks))
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
              if L.mem c l
              then marker i, true
              else if placed
              then "|", true
              else "-", false
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
          Iter.fold
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
        Format.fprintf formatter "%s" (Buffer.contents total))
    ;;

    let print_csl formatter trace =
      let serialize f (l, _) =
        Iter.pp_seq
          ~sep:","
          (fun f v -> Format.fprintf f "%s" (C.to_string v))
          f
          (L.to_iter l)
      in
      Iter.pp_seq ~sep:",STEP," serialize formatter trace
    ;;

    let trace_to_vertical_svgbob ?(numbers = false) ~tasks clocks ch trace =
      if List.is_empty clocks
      then ()
      else (
        let marker =
          if numbers
          then fun _ j -> Int.to_string j
          else
            fun i _ ->
              match Int.rem i 9 with
              | 0 -> "*"
              | 1 -> "o"
              | 2 -> "◆"
              | 3 -> ">"
              | 4 -> "O"
              | 5 -> "^"
              | 6 -> "#"
              | 7 -> "<"
              | 8 -> "v"
              | _ -> failwith "unreachable"
        in
        let clocks =
          clocks
          |> List.filter (fun c ->
            not
              (List.exists
                 (fun (_, r, s, f, d) -> c = r || c = s || c = f || c = d)
                 tasks))
          |> Array.of_list
        in
        let width =
          List.fold_left
            (fun off (name, _, _, _, _) ->
               let s = C.to_string name in
               Format.fprintf ch "%*s\n" (off + String.grapheme_length s + 1) s;
               off + 8)
            0
            tasks
        in
        let width =
          Array.fold_left
            (fun off clock ->
               let s = C.to_string clock in
               Format.fprintf ch "%*s\n" (off + String.grapheme_length s) s;
               off + 2)
            width
            clocks
        in
        let _ =
          for _ = 1 to List.length tasks do
            Format.fprintf ch "-+---+--"
          done
        in
        let _ =
          for _ = 1 to Array.length clocks do
            Format.fprintf ch "+-"
          done
        in
        let _ = Format.fprintf ch "+\n" in
        let[@inline hint] serialize_record (tasks, clocks) (l, n) =
          let new_tasks =
            Array.map
              (fun ((name, r, s, f, d), executes, constrains) ->
                 let ready = L.mem r l
                 and start = L.mem s l
                 and finish = L.mem f l
                 and deadline = L.mem d l in
                 let now_executes = (executes || start) && not finish
                 and now_constrains = (constrains || ready) && not deadline in
                 let _ =
                   match executes, now_executes with
                   | false, true -> Format.fprintf ch ".+."
                   | true, true ->
                     Format.fprintf
                       ch
                       (if start then if finish then "###" else ".-." else "| |")
                   | false, false ->
                     Format.fprintf ch (if start && finish then "###" else " | ")
                   | true, false -> Format.fprintf ch "'+'"
                 in
                 Format.fprintf ch " ";
                 let _ =
                   match constrains, now_constrains with
                   | false, true -> Format.fprintf ch ".+."
                   | true, true ->
                     Format.fprintf
                       ch
                       (if ready then if deadline then ":=:" else ".-." else ": :")
                   | false, false ->
                     Format.fprintf ch (if ready && deadline then ".+." else " | ")
                   | true, false -> Format.fprintf ch "'+'"
                 in
                 Format.fprintf ch " ";
                 (name, r, s, f, d), now_executes, now_constrains)
              tasks
          in
          let horizontal = ref false in
          let new_clocks =
            Array.mapi
              (fun i (clock, count) ->
                 let count =
                   if L.mem clock l
                   then (
                     horizontal := true;
                     Format.fprintf ch "%s" (marker i count);
                     count + 1)
                   else (
                     Format.fprintf ch "+";
                     count)
                 in
                 Format.fprintf ch (if !horizontal then "-" else " ");
                 clock, count)
              clocks
          in
          let time_label = N.to_string n in
          Format.fprintf ch "+ %s\n" time_label;
          Array.iter
            (fun ((_, r, _, _, d), executes, constrains) ->
               let ready = L.mem r l
               and deadline = L.mem d l in
               Format.fprintf ch (if executes then "| | " else " |  ");
               Format.fprintf
                 ch
                 (if constrains
                  then ": : "
                  else if ready && deadline
                  then "'+' "
                  else " |  "))
            new_tasks;
          Array.iter (fun _ -> Format.fprintf ch "| ") new_clocks;
          Format.fprintf ch "|\n";
          new_tasks, new_clocks
        in
        let task_states =
          tasks |> List.map (fun task -> task, false, false) |> Array.of_list
        in
        let clock_states = Array.map (fun clock -> clock, 0) clocks in
        let _ = Iter.fold serialize_record (task_states, clock_states) trace in
        let _ =
          for _ = 0 to width do
            Format.fprintf ch " "
          done
        in
        Format.fprintf ch "v")
    ;;
  end
end

let%test_module _ =
  (module struct
    open Rtccsl
    open Number
    module A = Make (Clock.String) (Float)
    module S = Strategy (A)

    let step = 0.1

    let slow_strat =
      S.Solution.first @@ S.Num.slow ~upper_bound:2.0 ~ceil:(Float.round_up step)
    ;;

    let random_strat =
      S.Solution.random_label
        (S.Num.random_leap
           ~upper_bound:1.0
           ~ceil:(Float.round_up step)
           ~floor:(Float.round_down step)
           ~rand:Float.random)
    ;;

    let%test _ =
      let a = A.of_spec @@ Rtccsl.constraints_only [ Coincidence [ "a"; "b" ] ] in
      not (A.Trace.is_empty (A.gen_trace S.Var.none slow_strat a))
    ;;

    let%test _ =
      let a = A.of_spec @@ Rtccsl.constraints_only [ Coincidence [ "a"; "b" ] ] in
      not (A.Trace.is_empty (A.gen_trace S.Var.none slow_strat a))
    ;;

    let%test _ =
      let a = A.of_spec @@ Rtccsl.constraints_only [ Coincidence [ "a"; "b" ] ] in
      let trace = A.gen_trace S.Var.none random_strat a in
      not (A.Trace.is_empty trace)
    ;;

    (* let%test _ =
      let _, (g, _, _) =
        A.of_spec @@ Rtccsl.constraints_only [ Coincidence [ "a"; "b" ] ]
      in
      let v = A.empty_vars in
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0); *)
      not (Iter.is_empty (g v 0.0))
    ;; *)

    let%test _ =
      let empty1 =
        A.of_spec
          { constraints = [ Coincidence [ "a"; "b" ]; Exclusion [ "a"; "b" ] ]
          ; var_relations = []
          }
      in
      let empty2 = A.empty_sim in
      let steps = 10 in
      let trace =
        A.bisimulate S.Var.none slow_strat empty1 empty2 |> A.Trace.take ~steps
      in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Iter.length trace = steps
    ;;

    let%test _ =
      let sampling1 =
        A.of_spec
        @@ Rtccsl.constraints_only
             [ Delay { out = "o"; arg = "i"; delay = Const 0, Const 0; base = Some "b" } ]
      in
      let sampling2 =
        A.of_spec
        @@ Rtccsl.constraints_only [ Sample { out = "o"; arg = "i"; base = "b" } ]
      in
      let steps = 10 in
      let trace =
        A.bisimulate S.Var.none random_strat sampling1 sampling2 |> A.Trace.take ~steps
      in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Iter.length trace = steps
    ;;

    let%test _ =
      let a =
        A.of_spec @@ Rtccsl.constraints_only [ Precedence { cause = "a"; conseq = "b" } ]
      in
      let trace = A.gen_trace S.Var.none slow_strat a |> A.Trace.take ~steps:10 in
      (* let g, _, _ = a in *)
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0);
      Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace trace; *)
      Iter.length trace = 10
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

  let test_truncated a b mu sigma =
    let v = truncated_guassian_rvs ~a ~b ~mu ~sigma in
    a <= v && v <= b
  ;;

  let%test _ =
    let _ = Random.init 12312 in
    test_truncated (-1.0) 1.0 0.0 0.5
  ;;
end
