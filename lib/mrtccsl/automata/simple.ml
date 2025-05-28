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
    (* let _ =
      Printf.printf "%f %f %f %f %f %f %f\n" a b mu sigma prob_l prob_r sample_prob
    in *)
    let v = Owl.Stats.gaussian_ppf sample_prob ~mu ~sigma in
    (* Printf.printf "prob_l %f prob_r %f %f\n" prob_l prob_r sample_prob; *)
    if Float.is_nan v
    then failwith (Printf.sprintf "a: %f b: %f mu: %f sigma: %f gets nan!" a b mu sigma)
    else if Float.is_infinite v
    then failwith (Printf.sprintf "a: %f b: %f mu: %f sigma: %f gets inf!" a b mu sigma)
    else v)
;;

(**Specifies the distribution of the time variable. *)
type ('v, 't) dist = 'v * 't distribution [@@deriving map]

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

module type S = sig
  type clock
  type param
  type var
  type label

  module N : Num
  module I : Interval.I with type num := N.t
  module L : Set.S with type elt := clock and type t := label

  type num_cond = I.t
  type guard = (label * num_cond) list
  type solution = label * N.t
  type trace = solution Seq.t

  module Strategy : sig
    module Var : sig
      type t = var -> I.t -> I.t

      val none : t
      val use_dist : (var, N.t) dist list -> t
    end

    module Num : sig
      type t = num_cond -> N.t

      val random_leap
        :  upper_bound:N.t
        -> ceil:(N.t -> N.t -> N.t)
        -> floor:(N.t -> N.t -> N.t)
        -> rand:(N.t -> N.t -> N.t)
        -> t

      val slow : upper_bound:N.t -> ceil:(N.t -> N.t -> N.t) -> t
      val fast : upper_bound:N.t -> floor:(N.t -> N.t -> N.t) -> t
    end

    module Solution : sig
      type t = guard -> solution option

      val first : Num.t -> t
      val random_label : Num.t -> t
      val avoid_empty : t -> t
      val refuse_empty : t -> t
    end
  end

  type vars =
    { current : var -> I.t
    ; consume : var -> unit
    }

  type t = (vars -> N.t -> guard) * (vars -> N.t -> solution -> bool) * label
  type env = (var -> I.t) * t

  val empty : t
  val return_env : t -> env
  val empty_vars : vars
  val sync : t -> t -> t
  val of_constr : (clock, param, var, N.t) Rtccsl.constr -> t
  val of_spec : (clock, param, var, N.t) Rtccsl.specification -> env
  val gen_trace : Strategy.Var.t -> Strategy.Solution.t -> env -> trace
  val until_horizon : N.t -> trace -> trace * bool ref
  val bisimulate : Strategy.Var.t -> Strategy.Solution.t -> env -> env -> trace
end

module Make (C : ID) (N : Num) = struct
  type clock = C.t
  type param = C.t
  type var = C.t

  module N = N

  (*TODO: optimize the label solving*)
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
  type solution = label * N.t
  type trace = solution Seq.t

  type vars =
    { current : var -> I.t
      (**[current v] returns current range of variable [v]. Raises [Not_found] if not present. *)
    ; consume : var -> unit (**[consume v] invalidates the value *)
    }

  type t = (vars -> N.t -> guard) * (vars -> N.t -> solution -> bool) * label
  type env = (var -> I.t) * t

  open Sexplib0.Sexp_conv

  let sexp_of_label label = sexp_of_list C.sexp_of_t @@ L.elements label
  let sexp_of_solution = sexp_of_pair sexp_of_label N.sexp_of_t
  let sexp_of_trace trace = sexp_of_list sexp_of_solution trace
  let sexp_of_guard guard = sexp_of_list (sexp_of_pair sexp_of_label I.sexp_of_t) guard
  let noop_guard _ now = [ L.empty, I.inter (I.pinf N.zero) (I.pinf_strict now) ]
  let noop_transition _ n (_, n') = N.compare n n' < 0
  let empty : t = noop_guard, noop_transition, L.empty

  let variant_to_string (label, cond) =
    Printf.sprintf "%s ? %s" (L.to_string label) (I.to_string cond)
  ;;

  let guard_to_string variants = List.to_string ~sep:" || " variant_to_string variants

  let solution_to_string (label, now) =
    Printf.sprintf "%s ! %s" (L.to_string label) (N.to_string now)
  ;;

  let correctness_decorator a =
    let g, t, clocks = a in
    let t vars n (l, n') =
      let possible = g vars n in
      let proj = L.inter clocks l in
      let present =
        List.exists (fun (l', cond) -> L.equal proj l' && I.contains cond n') possible
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
    let g vars now =
      (* let _ = Printf.printf "sync--- at %s\n" (N.to_string now) in *)
      let g1 = g1 vars now in
      (* let _ = Printf.printf "sync sol 1: %s\n" (guard_to_string g1) in *)
      let g2 = g2 vars now in
      (* let _ = Printf.printf "sync sol 2: %s\n" (guard_to_string g2) in *)
      let pot_solutions = List.cartesian g1 g2 in
      let solutions = List.filter_map guard_solver pot_solutions in
      (* let _ = Printf.printf "sync sols: %s\n" (guard_to_string solutions) in *)
      solutions
    in
    let t vars n l = t1 vars n l && t2 vars n l in
    g, t, c
  ;;

  (** Logical-only guard function translates labels to guard of transition, adds generic [eta < eta'] condition on real-time.**)
  let lo_guard l _ now = List.map (fun l -> l, I.pinf_strict now) l

  let stateless labels =
    let g = lo_guard labels in
    g, fun _ _ _ -> true
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
    , fun _ _ (l, _) ->
        let delta = if L.mem c1 l then 1 else 0 in
        let delta = delta - if L.mem c2 l then 1 else 0 in
        let _ = c := !c + delta in
        !c >= 0 )
  ;;

  let of_constr constr : t =
    let open Rtccsl in
    let label_list = List.map L.of_list in
    let g, t =
      match constr with
      | Precedence { cause; conseq } -> prec cause conseq true
      | Causality { cause; conseq } -> prec cause conseq false
      | Exclusion clocks ->
        let l = label_list ([] :: List.map (fun x -> [ x ]) clocks) in
        stateless l
      | Coincidence clocks ->
        let l = label_list [ clocks; [] ] in
        stateless l
      | RTdelay { out = b; arg = a; delay } ->
        let queue = ref [] in
        let g _ now =
          if List.is_empty !queue
          then [ L.of_list [ a ], I.pinf_strict now; L.empty, I.pinf_strict now ]
          else (
            let next = List.hd !queue in
            [ L.of_list [ a ], Option.get (I.complement_left next)
            ; L.empty, Option.get (I.complement_left next)
            ; L.of_list [ a; b ], next
            ; L.of_list [ b ], next
            ])
        in
        let t vars _ (l, n') =
          let _ =
            if L.mem a l
            then (
              let v = vars.current delay in
              (* Printf.printf
                "generated %s %s at %s\n"
                (C.to_string delay)
                (I.to_string v)
                (N.to_string n'); *)
              (* Printf.printf "%s\n" (I.to_string (I.shift_by v n')); *)
              queue (*FIXME: this is an error*)
              := List.stable_sort
                   (fun n n' ->
                      N.compare
                        (Option.get @@ I.left_bound_opt n)
                        (Option.get @@ I.left_bound_opt n'))
                   (List.append !queue [ I.shift_by v n' ]);
              vars.consume delay)
          in
          let _ = if L.mem b l then queue := List.tl !queue in
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
            [ L.of_list [ out ], next; L.empty, Option.get (I.complement_left next) ]
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
          [ L.of_list [ out ], next; L.empty, Option.get (I.complement_left next) ]
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
          | None -> [ L.of_list [ c ], I.pinf_strict now; L.empty, I.pinf_strict now ]
          | Some v ->
            let next_after = N.(at_least + v) in
            [ ( L.of_list [ c ]
              , if strict then I.pinf_strict next_after else I.pinf next_after )
            ; (L.empty, I.(now <-> next_after))
            ]
        in
        let t _ _ (l, n') =
          let _ = if L.mem c l then last := Some n' in
          true
        in
        g, t
      | Periodic { out; base; period = Const period } ->
        let labels_eqp = label_list [ [ base; out ]; [] ] in
        let labels_lp = label_list [ [ base ]; [] ] in
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
          label_list [ []; [ arg ]; [ out; arg; base ]; [ out; base ] ]
        in
        let labels_unlatched = label_list [ []; [ arg ]; [ out; arg; base ]; [ base ] ] in
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
          let labels = label_list labels in
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
        let t _ _ (l, _) =
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
        let t _ _ (l, _) =
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
          let labels = label_list labels in
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
        let g n =
          let labels =
            if !last
            then [ []; [ base ] ]
            else [ []; [ out; arg; base ]; [ out; arg ]; [ arg ] ]
          in
          lo_guard (label_list labels) n
        in
        let t _ _ (l, _) =
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

  let of_spec spec =
    let constraints =
      List.fold_left sync empty (List.map of_constr Rtccsl.(spec.constraints))
    and relations =
      spec.var_relations
      |> List.map of_var_rel
      |> List.fold_left (CMap.union (fun _ x y -> Some (I.inter x y))) CMap.empty
    in
    (fun v -> Option.value ~default:I.inf (CMap.find_opt v relations)), constraints
  ;;

  module Strategy = struct
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
      type t = num_cond -> N.t

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

      let rec first num_decision = function
        | [] -> None
        | (l, c) :: tail ->
          if L.is_empty l
          then (
            match first num_decision tail with
            | None ->
              let n = num_decision c in
              Some (l, n)
            | Some x -> Some x)
          else (
            let n = num_decision c in
            Some (l, n))
      ;;

      let random_label num_decision solutions =
        if List.is_empty solutions
        then None
        else (
          let len = List.length solutions in
          let choice = Random.int len in
          let l, c = List.nth solutions choice in
          let n = num_decision c in
          Some (l, n))
      ;;

      let avoid_empty s variants =
        let empty, others =
          List.partition_map
            (fun (l, c) ->
               if L.is_empty l then Either.Left (l, c) else Either.Right (l, c))
            variants
        in
        Option.bind_or (s others) (fun () -> s empty)
      ;;

      let refuse_empty s variants =
        let variants = List.filter (fun (l, _) -> not (L.is_empty l)) variants in
        s variants
      ;;

      let debug f variants =
        let _ = Printf.printf "variants at strategy: %s\n" (guard_to_string variants) in
        f variants
      ;;
    end
  end

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
    if List.is_empty possible
    then None
    else
      let* sol = strat possible in
      (* let _ = Printf.printf "decision: %s\n" (solution_to_string sol) in *)
      if transition vars now sol then Some sol else None
  ;;

  let empty_vars = { current = (fun _ -> failwith "none"); consume = (fun _ -> ()) }

  let vars_from_rels (strat : Strategy.Var.t) (var2cond : var -> I.t) =
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

  let gen_trace var_strat (sol_strat : Strategy.Solution.t) (vrel, a) : trace =
    Seq.unfold
      (fun (vars, now) ->
         let* l, now = next_step sol_strat a vars now in
         Some ((l, now), (vars, now)))
      (vars_from_rels var_strat vrel, N.neg N.one)
  ;;

  let until_horizon time trace =
    let was_cut = ref false in
    ( Seq.take_while
        (fun (_, n) ->
           if N.less n time
           then true
           else (
             was_cut := true;
             false))
        trace
    , was_cut )
  ;;

  let bisimulate var_strat s (vrel, a1) (_, a2) =
    let _, trans, _ = a2 in
    Seq.unfold
      (fun (vars, now) ->
         let* l, n = next_step s a1 vars now in
         if trans vars now (l, n) then Some ((l, n), (vars, n)) else None)
      (vars_from_rels var_strat vrel, N.zero)
  ;;

  (*TODO: investigate relation between the vrel1 and vrel2. *)

  let accept_trace (rval, a) n t =
    let step a vars n sol =
      let _, transition, _ = a in
      transition vars n sol
    in
    let _, result =
      List.fold_left
        (fun (vars, n) (l, n') ->
           match n with
           | Some n -> if step a vars n (l, n') then vars, Some n' else vars, None
           | None -> vars, None)
        (vars_from_rels (fun _ c -> c) rval, Some n)
        t
    in
    result
  ;;

  let return_env a = (fun _ -> failwith "not implemented"), a
  let proj_trace clocks trace = Seq.map (fun (l, n) -> L.inter clocks l, n) trace
  let skip_empty trace = Seq.filter (fun (l, _) -> not (L.is_empty l)) trace

  (*TODO: translate into a printer. *)
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
        Seq.fold_left
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

  (*TODO: translate into a printer https://ocaml.org/manual/5.3/api/Printf.html *)
  let trace_to_csl trace =
    let serialize (l, _) = List.to_string ~sep:"," C.to_string (L.to_list l) in
    Seq.to_string ~sep:",STEP," serialize trace
  ;;
end

let%test_module _ =
  (module struct
    open Rtccsl
    open Number
    module A = Make (Clock.String) (Float)

    let step = 0.1

    let slow_strat =
      A.Strategy.Solution.first
      @@ A.Strategy.Num.slow ~upper_bound:2.0 ~ceil:(Float.round_up step)
    ;;

    let random_strat =
      A.Strategy.Solution.random_label
        (A.Strategy.Num.random_leap
           ~upper_bound:1.0
           ~ceil:(Float.round_up step)
           ~floor:(Float.round_down step)
           ~rand:Float.random)
    ;;

    let%test _ =
      let a = A.return_env @@ A.of_constr (Coincidence [ "a"; "b" ]) in
      not (Seq.is_empty (A.gen_trace A.Strategy.Var.none slow_strat a))
    ;;

    let%test _ =
      let a = A.return_env @@ A.of_constr (Coincidence [ "a"; "b" ]) in
      not (Seq.is_empty (A.gen_trace A.Strategy.Var.none slow_strat a))
    ;;

    let%test _ =
      let a = A.return_env @@ A.of_constr (Coincidence [ "a"; "b" ]) in
      let trace = A.gen_trace A.Strategy.Var.none random_strat a in
      not (Seq.is_empty trace)
    ;;

    let%test _ =
      let g, _, _ = A.of_constr (Coincidence [ "a"; "b" ]) in
      let v = A.empty_vars in
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0); *)
      not (List.is_empty (g v 0.0))
    ;;

    let%test _ =
      let empty1 =
        A.of_spec
          { constraints = [ Coincidence [ "a"; "b" ]; Exclusion [ "a"; "b" ] ]
          ; var_relations = []
          }
      in
      let empty2 = A.return_env @@ A.empty in
      let steps = 10 in
      let trace =
        A.bisimulate A.Strategy.Var.none slow_strat empty1 empty2 |> Seq.take steps
      in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Seq.length trace = steps
    ;;

    let%test _ =
      let sampling1 =
        A.of_constr
        @@ Delay { out = "o"; arg = "i"; delay = Const 0, Const 0; base = Some "b" }
      in
      let sampling2 = A.of_constr @@ Sample { out = "o"; arg = "i"; base = "b" } in
      let steps = 10 in
      let trace =
        A.bisimulate
          A.Strategy.Var.none
          random_strat
          (A.return_env @@ sampling1)
          (A.return_env @@ sampling2)
        |> Seq.take steps
      in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Seq.length trace = steps
    ;;

    let%test _ =
      let a = A.of_constr (Precedence { cause = "a"; conseq = "b" }) in
      let trace =
        A.gen_trace A.Strategy.Var.none slow_strat (A.return_env @@ a) |> Seq.take 10
      in
      (* let g, _, _ = a in *)
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0);
      Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace trace; *)
      Seq.length trace = 10
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
