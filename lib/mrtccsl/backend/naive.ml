open Prelude
open Language

let factor = 1000.0

let truncated_distribution ~a ~b ~cdf ~ppf =
  let a, b = factor *. a, factor *. b in
  let prob_l, prob_r = Tuple.map2 cdf (a, b) in
  if Float.abs (prob_r -. prob_l) < 0.000001
  then Random.float (b -. a) +. a
  else (
    let sample_prob = Owl.Stats.uniform_rvs ~a:prob_l ~b:prob_r in
    let result = ppf sample_prob in
    result /. factor)
;;

let truncated_guassian_rvs ~a ~b ~mu ~sigma =
  if Float.equal sigma 0.0
  then mu
  else (
    let mu, sigma = factor *. mu, factor *. sigma in
    let cdf = Owl.Stats.gaussian_cdf ~mu ~sigma in
    let ppf = Owl.Stats.gaussian_ppf ~mu ~sigma in
    truncated_distribution ~a ~b ~cdf ~ppf)
;;

let truncated_exponential_rvs ~a ~b ~rate =
  let lambda = rate /. factor in
  let cdf = Owl.Stats.exponential_cdf ~lambda in
  let ppf = Owl.Stats.exponential_ppf ~lambda in
  let result = truncated_distribution ~a ~b ~cdf ~ppf in
  result
;;

(**Specifies the distribution of the time variable. *)
type ('v, 't) dist_binding = 'v * 't distribution [@@deriving map]

module type ID = sig
  open Interface
  include OrderedType
  include Stringable with type t := t
  include Parseble with type t := t
  include Sexplib0.Sexpable.S with type t := t
end

module type Num = sig
  include Interval.Num
  include Interface.ExpOrder.S with type t := t
  include Interface.Stringable with type t := t
  include Interface.Parseble with type t := t
  include Interface.OrderedType with type t := t

  val zero : t
  val one : t
  val minus_one : t
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

module type S = sig
  module C : ID

  type clock = C.t
  type param = C.t
  type var = C.t

  module N : Num
  module NI : Interval.I with type num = N.t
  module II : Interval.I with type num = int
  module L : Label with type elt := clock

  type guard = (L.t * NI.t) Iter.t
  type solution = L.t * N.t
  type sol_strategy = guard -> solution option

  type t =
    { name : string
    ; guard : N.t -> guard
    ; transition : N.t -> solution -> bool
    ; clocks : L.t
    ; print_state : unit -> string
    }

  type sim

  val empty_sim : sim

  val of_spec
    :  ?debug:bool
    -> (clock, param, param, var, var, N.t) Language.Specification.t
    -> sim

  type trace = (L.t, N.t) Trace.t

  val gen_trace : sol_strategy -> sim -> trace
  val bisimulate : sol_strategy -> sim -> sim -> trace
  val accept_trace : sim -> trace -> bool
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

    module E = C
  end

  module NI = struct
    include Interval.MakeDebug (N)

    let of_var_rel =
      let open Language in
      function
      | NumRelation (v, rel, Const c) ->
        let cond_f =
          match rel with
          | `Less -> ninf_strict
          | `LessEq -> ninf
          | `More -> pinf_strict
          | `MoreEq -> pinf
          | `Eq -> return
          | `Neq ->
            failwith "non-equality is irrepresentable in interval domain, not convex"
        in
        let cond = cond_f c in
        v, cond
      | _ -> failwith "numeric relations between rational variables are not implemented"
    ;;
  end

  module II = struct
    include Interval.MakeDebug (Number.Integer)

    let of_var_rel =
      let open Language in
      function
      | NumRelation (v, rel, Const c) ->
        let cond_f =
          match rel with
          | `Less -> ninf_strict
          | `LessEq -> ninf
          | `More -> pinf_strict
          | `MoreEq -> pinf
          | `Eq -> return
          | `Neq ->
            failwith "non-equality is irrepresentable in interval domain, not convex"
        in
        let cond = cond_f c in
        v, cond
      | _ -> failwith "numeric relations between integer variables are not implemented"
    ;;

    let to_nonstrict = function
      | Bound (left, right) ->
        let left =
          match left with
          | Include left -> left
          | Exclude left -> succ left
          | Inf -> failwith "to_nonstrict: [-oo, x] is not bound"
        and right =
          match right with
          | Include right -> right
          | Exclude right -> pred right
          | Inf -> failwith "to_nonstrict: [x, +oo] is not bound"
        in
        left, right
      | Empty -> failwith "to_nonstrict: interval is empty"
    ;;
  end

  module CMap = Map.Make (C)

  type label = L.t
  type num_cond = NI.t
  type guard = (label * num_cond) Iter.t
  type solution = label * N.t
  type sol_strategy = guard -> solution option
  type trace = (L.t, N.t) Trace.t

  module VarSeq = struct
    type 'v t =
      { bounds : 'v
      ; process : 'v -> 'v
      ; mutable suppress : bool
      ; mutable instances : (int, 'v * int) Hashtbl.t
      ; mutable subscribers : int
      }

    type 'v container = { mutable vars : 'v t CMap.t }

    let empty_container () = { vars = CMap.empty }

    let declare_variable container var (bounds, process) =
      container.vars
      <- CMap.add
           var
           { bounds
           ; process
           ; suppress = false
           ; instances = Hashtbl.create 0
           ; subscribers = 0
           }
           container.vars
    ;;

    let suppress container = CMap.iter (fun _ seq -> seq.suppress <- true) container.vars

    let unsuppress container =
      CMap.iter (fun _ seq -> seq.suppress <- false) container.vars
    ;;

    let subscribe container var =
      let seq = CMap.find var container.vars in
      seq.subscribers <- seq.subscribers + 1;
      seq
    ;;

    let peek_value seq index =
      let v, _ =
        Hashtbl.value_mut
          ~default:(fun () ->
            let value = if seq.suppress then seq.bounds else seq.process seq.bounds in
            value, 0)
          index
          seq.instances
      in
      v
    ;;

    let pop_value seq index =
      let v, consumptions = Hashtbl.find seq.instances index in
      let consumptions = consumptions + 1 in
      if consumptions = seq.subscribers
      then Hashtbl.remove seq.instances index
      else Hashtbl.add seq.instances index (v, consumptions)
    ;;

    type 'v handle =
      { seq : 'v t
      ; mutable current : int
      }

    let current { seq; current } = peek_value seq current

    let consume h =
      let { seq; current } = h in
      pop_value seq current;
      h.current <- current + 1
    ;;

    let get_handle container var =
      let seq = subscribe container var in
      let h = { seq; current = 0 } in
      (fun () -> current h), fun () -> consume h
    ;;

    let get_handle_param return container = function
      | Var v -> get_handle container v
      | Const c ->
        let c = return c in
        (fun () -> c), fun () -> ()
    ;;
  end

  type t =
    { name : string
    ; guard : N.t -> guard
    ; transition : N.t -> solution -> bool
    ; clocks : L.t
    ; print_state : unit -> string
    }

  type sim =
    { durations : NI.t VarSeq.container
    ; integers : II.t VarSeq.container
    ; automata : t list
    }

  open Sexplib0.Sexp_conv

  let sexp_of_label label = sexp_of_list C.sexp_of_t @@ L.elements label
  let sexp_of_solution = sexp_of_pair sexp_of_label N.sexp_of_t
  let sexp_of_trace trace = sexp_of_list sexp_of_solution trace
  let sexp_of_guard guard = sexp_of_list (sexp_of_pair sexp_of_label NI.sexp_of_t) guard

  let noop_guard now =
    Iter.of_array [| L.empty, NI.inter (NI.pinf N.zero) (NI.pinf_strict now) |]
  ;;

  let noop_transition n (_, n') = N.compare n n' < 0

  let empty : t =
    { name = "noop"
    ; guard = noop_guard
    ; transition = noop_transition
    ; clocks = L.empty
    ; print_state = (fun () -> "empty")
    }
  ;;

  let empty_sim : sim =
    { durations = VarSeq.empty_container ()
    ; integers = VarSeq.empty_container ()
    ; automata = []
    }
  ;;

  let variant_to_string (label, cond) =
    Printf.sprintf "%s ? %s" (L.to_string label) (NI.to_string cond)
  ;;

  let guard_to_string variants = Iter.to_string ~sep:" || " variant_to_string variants

  let solution_to_string (label, now) =
    Printf.sprintf "%s ! %s" (L.to_string label) (N.to_string now)
  ;;

  let correctness_decorator a =
    let { name; guard; transition; clocks; print_state } = a in
    let transition n (l, n') =
      let possible = guard n in
      (* print_endline "----";
      print_endline @@ solution_to_string (l,n');
      print_endline @@ guard_to_string possible; *)
      let present =
        Iter.exists
          (fun (l', cond) ->
             let eq = L.equal_modulo ~modulo:clocks l l'
             and contains = NI.contains cond n' in
             (* Printf.printf "%b %b\n" eq contains; *)
             eq && contains)
          possible
      in
      present && transition n (l, n')
    in
    { name; guard; transition; clocks; print_state }
  ;;

  let debug_g name g now =
    let variants = g now in
    let _ = Printf.printf "<%s>: %s\n" name (guard_to_string variants) in
    variants
  ;;

  let[@inline always] sat_solver ~modulo l l' =
    if L.equal_modulo ~modulo l l' then Some (L.union l l') else None
  ;;

  let[@inline always] linear_solver c c' =
    let res = NI.inter (NI.pinf N.zero) (NI.inter c c') in
    if NI.is_empty res then None else Some res
  ;;

  let[@inline always] guard_solver ~modulo ((l, c), (l', c')) =
    match sat_solver ~modulo l l', linear_solver c c' with
    | Some l, Some c -> Some (l, c)
    | _ -> None
  ;;

  let sync (a1 : t) (a2 : t) : t =
    let { name = n1; guard = g1; transition = t1; clocks = c1; print_state = p1 } = a1 in
    let { name = n2; guard = g2; transition = t2; clocks = c2; print_state = p2 } = a2 in
    let c = L.union c1 c2 in
    let conf_surface = L.inter c1 c2 in
    let g now =
      let g1 = g1 now
      and g2 = g2 now in
      (* let _ = Printf.printf "before: %s\n" (guard_to_string g1) in *)
      let pot_solutions = Iter.product g1 g2 in
      let solutions = Iter.filter_map (guard_solver ~modulo:conf_surface) pot_solutions in
      (* let _ = Printf.printf "sync sols: %s\n" (guard_to_string solutions) in *)
      let solutions = Iter.persistent solutions in
      (* let _ = Printf.printf "after: %s\n" (guard_to_string solutions) in *)
      solutions
    in
    let t n l = t1 n l && t2 n l in
    { name = Printf.sprintf "sync(%s, %s)" n1 n2
    ; guard = g
    ; transition = t
    ; clocks = c
    ; print_state = (fun () -> Printf.sprintf "%s\n%s" (p1 ()) (p2 ()))
    }
  ;;

  let sync_guards ?(debug = true) (automata : t list) now =
    let solutions, _ =
      try
        List.fold_lefti
          (fun (prev_solutions, prev_clocks) i { guard; clocks; name; _ } ->
             (* let _ = print_endline (L.to_string clocks) in *)
             (* let _ = Printf.printf "before: %i\n" (Iter.length prev_solutions) in *)
             let conf_surface = L.inter prev_clocks clocks in
             let next_solutions = guard now in
             let pot_solutions = Iter.product prev_solutions next_solutions in
             let solutions =
               Iter.filter_map (guard_solver ~modulo:conf_surface) pot_solutions
             in
             let solutions = Iter.persistent solutions in
             if debug
             then
               if Iter.length solutions = 0
               then (
                 Printf.printf "now: %s\n" (N.to_string now);
                 Printf.printf "prev clocks: %s\n" (L.to_string prev_clocks);
                 Printf.printf "prev: %s\n" (guard_to_string prev_solutions);
                 Printf.printf "next clocks: %s\n" (L.to_string clocks);
                 Printf.printf "next: %s\n" (guard_to_string next_solutions);
                 Printf.printf "deadlock detected from constraint %s %i\n" name i;
                 failwith "need to fail here");
             (* let _ = Printf.printf "after: %i\n" (Iter.length solutions) in *)
             solutions, L.union prev_clocks clocks)
          (noop_guard now, L.empty)
          automata
      with
      | _ -> Iter.empty, L.empty
    in
    solutions
  ;;

  let print_state (automata : t list) () =
    List.filter_map
      (fun { print_state; name; _ } ->
         let state_str = print_state () in
         if String.is_empty state_str
         then None
         else Some (Printf.sprintf "[%s]: %s" name state_str))
      automata
    |> List.to_string ~sep:"\n" Fun.id
  ;;

  let sync_transitions (automata : t list) before sol =
    List.for_all
      (fun { transition; name; print_state; _ } ->
         let res = transition before sol in
         if not res
         then (
           Printf.printf
             "failed transition at %s: %s %s\n"
             name
             (N.to_string before)
             (solution_to_string sol);
           print_endline @@ print_state ());
         res)
      automata
  ;;

  (** Logical-only guard function translates labels to guard of transition, adds generic [eta < eta'] condition on real-time.*)
  let lo_guard l =
    let l = Array.map (fun l -> l, NI.pinf N.zero) l in
    fun _ -> l
  ;;

  let stateless labels =
    let g = lo_guard labels in
    g, (fun _ _ -> true), fun () -> ""
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
    let p () = string_of_int !c in
    ( g
    , (fun _ (l, _) ->
        let delta = if L.mem c1 l then 1 else 0 in
        let delta = delta - if L.mem c2 l then 1 else 0 in
        let _ = c := !c + delta in
        !c >= 0)
    , p )
  ;;

  let of_constr (integers, durations) constr : t =
    let open Language in
    let label_array l = Array.map L.of_list (Array.of_list l) in
    let clocks = L.of_list (clocks constr) in
    let guard, transition, printer =
      match constr with
      | Precedence { cause; conseq } -> prec cause conseq true
      | Causality { cause; conseq } -> prec cause conseq false
      | Exclusion { args; _ } ->
        let l = label_array ([] :: List.map (fun x -> [ x ]) args) in
        stateless l
      | Coincidence clocks ->
        let l = label_array [ clocks; [] ] in
        stateless l
      | RTdelay { out = b; arg = a; delay } ->
        let current_delay, consume_delay =
          VarSeq.get_handle_param NI.return durations delay
        in
        let module Heap =
          Heap (struct
            include NI

            let compare n n' =
              N.compare
                (Option.get @@ NI.left_bound_opt n)
                (Option.get @@ NI.left_bound_opt n')
            ;;
          end)
        in
        let queue = Heap.create () in
        let g now =
          match Heap.peek queue with
          | None -> [| L.singleton a, NI.pinf_strict now; L.empty, NI.pinf_strict now |]
          | Some next ->
            [| L.singleton a, Option.get (NI.complement_left next)
             ; L.empty, Option.get (NI.complement_left next)
             ; L.doubleton a b, next
             ; L.singleton b, next
            |]
        in
        let t _ (l, n') =
          let _ =
            if L.mem a l
            then (
              Heap.add queue (NI.shift_by (current_delay ()) n');
              consume_delay ())
          in
          let _ = if L.mem b l then ignore (Heap.pop_min queue) in
          true
        in
        let p () = List.to_string NI.to_string (Heap.to_list queue) in
        g, t, p
      | CumulPeriodic { out; period; error; offset } ->
        let current_offset, consume_offset =
          VarSeq.get_handle_param NI.return durations offset
        and current_error, consume_error =
          VarSeq.get_handle_param NI.return durations error
        in
        let last = ref None in
        let g _ =
          let next =
            match !last with
            | None -> current_offset ()
            | Some v -> NI.shift_by (current_error ()) N.(v + period)
          in
          let g =
            [| L.singleton out, next; L.empty, Option.get (NI.complement_left next) |]
          in
          (* let _ = Printf.printf "%s: %s\n" (C.to_string period) (guard_to_string g) in  *)
          g
        in
        let t _ (l, n') =
          let _ =
            if L.mem out l
            then (
              if Option.is_none !last then consume_offset () else consume_error ();
              last := Some n')
          in
          true
        in
        let p () =
          Printf.sprintf
            "last: %s, current: %s"
            (Option.to_string ~default:"" N.to_string !last)
            (NI.to_string (current_error ()))
        in
        g, t, p
      | AbsPeriodic { out; period; error; offset } ->
        let current_offset, consume_offset =
          VarSeq.get_handle_param NI.return durations offset
        and current_error, consume_error =
          VarSeq.get_handle_param NI.return durations error
        in
        let last = ref None in
        let g _ =
          let next =
            match !last with
            | None -> current_offset ()
            | Some v -> NI.shift_by (current_error ()) N.(v + period)
          in
          [| L.singleton out, next; L.empty, Option.get (NI.complement_left next) |]
        in
        let t _ (l, n') =
          let _ =
            if L.mem out l
            then (
              let update =
                match !last with
                | None ->
                  consume_offset ();
                  n'
                | Some last ->
                  consume_error ();
                  N.(last + period)
              in
              last := Some update)
          in
          true
        in
        let p () =
          Printf.sprintf
            "last: %s, current: %s"
            (Option.to_string ~default:"" N.to_string !last)
            (NI.to_string (current_error ()))
        in
        g, t, p
      | Sporadic { out = c; at_least } ->
        let current_delay, consume_delay =
          VarSeq.get_handle_param NI.return durations at_least
        in
        let last = ref None in
        let g now =
          match !last with
          | None -> [| L.singleton c, NI.pinf_strict now; L.empty, NI.pinf_strict now |]
          | Some v ->
            let next_after = NI.shift_by (current_delay ()) v in
            [| L.singleton c, next_after
             ; L.empty, Option.get (NI.complement_left next_after)
            |]
        in
        let t _ (l, n') =
          let _ =
            if L.mem c l
            then (
              last := Some n';
              consume_delay ())
          in
          true
        in
        let p () =
          Printf.sprintf "last: %s" (Option.to_string ~default:"" N.to_string !last)
        in
        g, t, p
      | Periodic { out; base; period; _ } ->
        let labels_eqp = label_array [ [ base; out ]; [] ] in
        let labels_lp = label_array [ [ base ]; [] ] in
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
        let p () = string_of_int !c in
        g, t, p
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
        let t _ (l, _) =
          let _ = if L.mem arg l then latched := true in
          let _ = if L.mem base l then latched := false in
          true
        in
        let p () = string_of_bool !latched in
        g, t, p
      | Delay { out; arg; delay; base } ->
        let current_delay, consume_delay =
          VarSeq.get_handle_param II.return integers delay
        in
        (* let _ = assert (d1 <= d2) in *)
        let diff_base = C.compare base arg <> 0 in
        let module Heap =
          Heap (struct
            type t = int * int

            let compare = Tuple.compare_same2 Int.compare
          end)
        in
        let latch = ref None in
        let queue = Heap.create () in
        let labels_empty = [ []; [ arg ]; [ arg; base ]; [ base ] ] in
        let labels_ne_can = [ []; [ arg ]; [ arg; base ]; [ out; base ]; [ base ] ] in
        let labels_ne_must = [ [ out; base ]; [ out; arg; base ]; [] ] in
        let g now =
          let labels =
            match Heap.peek queue, II.to_nonstrict (current_delay ()) with
            | None, (0, 0) when diff_base -> [ []; [ arg ]; [ out; arg; base ]; [ base ] ]
            | None, (0, 0) -> [ []; [ out; arg ] ]
            | None, (0, _) -> [ []; [ arg ]; [ out; arg; base ]; [ base ]; [ arg; base ] ]
            | None, _ -> labels_empty
            | Some (_, 0), _ -> labels_ne_must
            | Some (x, _), _ when x <= 0 -> labels_ne_can
            | Some _, _ -> labels_empty
          in
          let labels = label_array labels in
          lo_guard labels now
        in
        let t _ (l, _) =
          let _ =
            if L.mem arg l then latch := Some (II.to_nonstrict (current_delay ()))
          in
          if L.mem base l
          then (
            Option.iter
              (fun delay ->
                 Heap.add queue delay;
                 consume_delay ())
              !latch;
            latch := None);
          let test1 =
            if L.mem out l
            then (
              match Heap.pop_min queue with
              | None -> false
              | Some (x, _) -> x <= 0)
            else true
          in
          let test2 =
            if L.mem base l
            then
              not
                (Heap.map (fun (x, y) -> x - 1, y - 1) queue;
                 Heap.exists (fun (_, y) -> y < 0) queue)
            else true
          in
          test1 && test2
        in
        let p () =
          let interval_str (l, r) = Printf.sprintf "[%i, %i]" l r in
          Printf.sprintf
            "latched: %s, heap: %s"
            (Option.to_string ~default:"empty" interval_str !latch)
            (List.to_string interval_str (Heap.to_list queue))
        in
        g, t, p
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
      | DisjunctiveUnion { out; args; _ } ->
        let labels = [] :: List.map (fun c -> [ out; c ]) args in
        stateless (label_array labels)
      | Alternate { first = a; second = b; strict } ->
        let phase = ref false in
        let g n =
          let labels =
            if not !phase
            then [| L.empty; L.singleton a |]
            else if strict
            then [| L.empty; L.singleton b |]
            else [| L.empty; L.singleton b; L.of_list [ a; b ] |]
          in
          lo_guard labels n
        in
        let t _ (l, _) =
          if L.mem b l then phase := false;
          if L.mem a l then phase := true;
          true
        in
        let p () = string_of_bool !phase in
        g, t, p
      | Fastest { out; args } | Slowest { out; args } ->
        let args_label = L.of_list args in
        let state = ref (args, [], CMap.of_list (List.map (fun x -> x, 0) args)) in
        let pws = List.powerset args in
        let g_fast () =
          let fastest_clocks, other_clocks, _ = !state in
          let out_labels =
            [] :: List.map (List.cons out) (List.powerset_nz fastest_clocks)
          in
          let useless_labels = List.powerset other_clocks in
          Seq.product (List.to_seq out_labels) (List.to_seq useless_labels)
          |> Seq.map (Tuple.fn2 List.append)
          |> List.of_seq
        in
        let t cond _ (l, _) =
          let _, _, count = !state in
          let count = if L.mem out l then CMap.map Int.pred count else count in
          let count =
            L.fold (CMap.entry ~default:0 Int.succ) (L.inter args_label l) count
          in
          let correct = ref true in
          let fastest_clocks, other =
            count
            |> CMap.to_list
            |> List.partition_map (fun (c, i) ->
              if i = 0
              then Either.Left c
              else (
                if cond i then correct := false;
                Either.Right c))
          in
          state := fastest_clocks, other, count;
          !correct
        in
        let g_slow () =
          let slowest_clocks, _, _ = !state in
          List.map (fun l -> if l = slowest_clocks then out :: l else l) pws
        in
        let g_without_n, t =
          match constr with
          | Fastest _ -> g_fast, t (fun i -> i > 0)
          | Slowest _ -> g_slow, t (fun i -> i < 0)
          | _ -> failwith "unreachable"
        in
        let g n =
          let labels = g_without_n () in
          let labels = label_array labels in
          lo_guard labels n
        in
        let p () =
          let _, _, count = !state in
          CMap.to_string C.to_string string_of_int count
        in
        g, t, p
      | Allow { left = from; right = until; args }
      | Forbid { left = from; right = until; args } ->
        let left_strict = false
        and right_strict = true in
        let folds = ref 0 in
        let eventwith = [] in
        let eventwith = if left_strict then eventwith else [ from ] :: eventwith in
        let eventwith = if right_strict then eventwith else [ until ] :: eventwith in
        let eventwith =
          if right_strict && left_strict then eventwith else [ from; until ] :: eventwith
          (*TODO: I am not extremely sure; this essentially means that there is a microstep order and until happens before from and everything else is around it. Same in forbid. *)
        in
        let without = [] in
        let without = if left_strict then [ from ] :: without else without in
        let without = if right_strict then [ until ] :: without else without in
        let without =
          if right_strict && left_strict then [ from; until ] :: without else without
        in
        let on inner outer =
          label_array
          @@ List.append outer
          @@ List.flat_cartesian ([] :: inner) (List.powerset args)
        and off inner outer =
          label_array
          @@ List.append ([] :: outer)
          @@ List.flat_cartesian inner (List.powerset args)
        and allow_more = label_array @@ List.powerset (from :: until :: args)
        and forbid_more = label_array @@ List.powerset [ from; until ] in
        let g =
          match constr with
          | Allow _ ->
            fun n ->
              let labels =
                match !folds with
                | 0 -> off eventwith without
                | 1 -> on eventwith without
                | _ -> allow_more
              in
              lo_guard labels n
          | Forbid _ ->
            fun n ->
              let labels =
                match !folds with
                | 0 -> on without eventwith
                | 1 -> off without eventwith
                | _ -> forbid_more
              in
              lo_guard labels n
          | _ -> failwith "unreachable"
        in
        let t _ (l, _) =
          let from_test = L.mem from l in
          let until_test = L.mem until l in
          let counter = !folds in
          let counter = if until_test then counter - 1 else counter in
          let counter = if from_test then counter + 1 else counter in
          let counter = if counter < 0 then 0 else counter in
          folds := counter;
          true
        in
        let p () = string_of_int !folds in
        g, t, p
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
        let t _ (l, _) =
          let _ = if L.mem arg l then sampled := true in
          let _ = if L.mem base l then sampled := false in
          true
        in
        let p () = string_of_bool !sampled in
        g, t, p
      | LastSampled { out; arg; base } ->
        let last = ref false in
        let g n =
          let labels =
            if !last
            then [ []; [ base ] ]
            else [ []; [ out; arg; base ]; [ out; arg ]; [ arg ] ]
          in
          lo_guard (label_array labels) n
        in
        let t _ (l, _) =
          let _ = if L.mem out l then last := true in
          let _ = if L.mem base l then last := false in
          true
        in
        let p () = string_of_bool !last in
        g, t, p
      | Subclocking { sub = a; super = b; _ } ->
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
                   | Some _ ->
                     failwithf
                       "pool constraint: lock->unlock pairs has to be injective, pair \
                        %s->%s is not"
                       (C.to_string from)
                       (C.to_string into)
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
          |> Iter.of_list
          |> Iter.flat_map (fun to_free ->
            let available = free_now + List.length to_free in
            List.powerset locks
            |> Iter.of_list
            |> Iter.filter_map (fun l ->
              if List.length l > available then None else Some (to_free @ l)))
          |> Iter.map (fun l -> L.of_list l, NI.pinf_strict now)
          |> Iter.to_dynarray
          |> Dynarray.to_array
        in
        let t _ (l, _) =
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
          true
        in
        let p () = List.to_string C.to_string !resources in
        g, t, p
    in
    let guard now = Iter.of_array (guard now) in
    correctness_decorator
      { name =
          (constr_to_string
             C.to_string
             C.to_string
             C.to_string
             C.to_string
             C.to_string
             N.to_string)
            constr
      ; guard
      ; transition
      ; clocks
      ; print_state = printer
      }
  ;;

  let debug_automata a = { a with guard = debug_g a.name a.guard }

  let discr_dist_value ratios interval =
    let left, right = II.to_nonstrict interval in
    let available =
      List.filter (fun (value, _) -> left <= value && value <= right) ratios
    in
    let sum = List.fold_left (fun acc (_, ratio) -> acc + ratio) 0 available in
    let choice = Random.int sum in
    let chosen, _ =
      List.fold_left
        (fun (chosen, choice) (value, ratio) ->
           match chosen with
           | Some _ as x -> x, choice
           | None ->
             let choice = choice - ratio in
             if choice < 0 then Some value, choice else None, choice)
        (None, choice)
        available
    in
    Option.get chosen
  ;;

  let cont_dist_value = function
    | Uniform ->
      fun cond ->
        let lower, upper =
          Option.unwrap ~expect:"uniform distribution is undefined on exclusive intervals"
          @@ NI.constant_bounds cond
        in
        N.random lower upper
    | Normal { mean; deviation } ->
      let mu = N.to_float mean in
      let sigma = N.to_float deviation in
      fun cond ->
        let bounds =
          Option.unwrap ~expect:"gaussian distribution is undefined on exclusive bounds"
          @@ NI.constant_bounds cond
        in
        let a, b = Tuple.map2 N.to_float bounds in
        let sample = truncated_guassian_rvs ~a ~b ~mu ~sigma in
        N.of_float sample
    | Exponential { rate } ->
      let rate = N.to_float rate in
      fun cond ->
        let bounds =
          Option.unwrap
            ~expect:"exponential distribution is undefined on exclusive bounds"
          @@ NI.constant_bounds cond
        in
        let a, b = Tuple.map2 N.to_float bounds in
        let sample = truncated_exponential_rvs ~a ~b ~rate in
        N.of_float sample
  ;;

  let of_spec ?(debug = false) spec : sim =
    let duration_bounds =
      Language.Specification.(spec.duration)
      |> List.map NI.of_var_rel
      |> List.fold_left
           (fun acc (v, rel) -> CMap.entry ~default:rel (NI.inter rel) v acc)
           CMap.empty
    and integer_bounds =
      Language.Specification.(spec.integer)
      |> List.map II.of_var_rel
      |> List.fold_left
           (fun acc (v, rel) -> CMap.entry ~default:rel (II.inter rel) v acc)
           CMap.empty
    and integer_dists, duration_dists =
      List.partition_map
        (function
          | DiscreteProcess { name; ratios } -> Either.Left (name, discr_dist_value ratios)
          | ContinuousProcess { name; dist } -> Either.Right (name, cont_dist_value dist))
        spec.probabilistic
    in
    let integer_dists, duration_dists =
      CMap.of_list integer_dists, CMap.of_list duration_dists
    in
    let durations = VarSeq.empty_container ()
    and integers = VarSeq.empty_container () in
    let process_combination inf return _ bounds dist =
      let bounds = Option.value ~default:inf bounds
      and process =
        Option.map_or ~default:Fun.id (fun dist cond -> return @@ dist cond) dist
      in
      Some (bounds, process)
    in
    CMap.merge (process_combination NI.inf NI.return) duration_bounds duration_dists
    |> CMap.iter (VarSeq.declare_variable durations);
    CMap.merge (process_combination II.inf II.return) integer_bounds integer_dists
    |> CMap.iter (VarSeq.declare_variable integers);
    let constraints =
      List.map (of_constr (integers, durations)) Language.Specification.(spec.logical)
    in
    { durations
    ; integers
    ; automata = (if debug then List.map debug_automata constraints else constraints)
    }
  ;;

  let next_step strat (a : t list) now : solution option =
    let possible = sync_guards a now in
    if Iter.is_empty possible
    then None
    else
      let* sol = strat possible in
      if sync_transitions a now sol then Some sol else None
  ;;

  let gen_trace (sol_strat : sol_strategy) { automata; integers; durations } : trace =
    VarSeq.unsuppress integers;
    VarSeq.unsuppress durations;
    Seq.unfold
      (fun now ->
         let* label, time = next_step sol_strat automata now in
         Some (Trace.{ label; time }, now))
      (N.minus_one)
  ;;

  let bisimulate s { automata = a1; _ } { automata = a2; _ } : trace =
    (*TODO: investigate relation between the vrel1 and vrel2. *)
    Seq.unfold
      (fun now ->
         let* label, time = next_step s a1 now in
         if sync_transitions a2 now (label, time)
         then Some (Trace.{ label; time }, time)
         else None)
      N.zero
  ;;

  let accept_trace { automata; integers; durations } (t : trace) =
    VarSeq.suppress integers;
    VarSeq.suppress durations;
    let step a n sol = sync_transitions a n sol in
    let result =
      Seq.fold_left
        (fun n Trace.{ label; time } ->
           match n with
           | Some n -> if step automata n (label, time) then Some time else None
           | None -> None)
        (Some N.minus_one)
        t
    in
    Option.is_some result
  ;;

  let proj_trace clocks trace = Iter.map (fun (l, n) -> L.inter clocks l, n) trace
  let skip_empty trace = Iter.filter (fun (l, _) -> not (L.is_empty l)) trace
  let to_string { automata; _ } = print_state automata ()

  let try_force_clock { automata; _ } now clock =
    let clock_automaton =
      { guard = (fun _ -> Iter.singleton (L.singleton clock, NI.inf))
      ; transition = (fun _ (l, _) -> L.mem clock l)
      ; clocks = L.singleton clock
      ; print_state = (fun () -> "")
      ; name = Printf.sprintf "force %s" (C.to_string clock)
      }
    in
    let automata = clock_automaton :: automata in
    sync_guards ~debug:true automata now
  ;;
end

module Strategy (A : S) = struct
  open A
  module CMap = Map.Make (A.C)

  type var = A.var
  type num = A.N.t

  module L = A.L
  module I = A.NI

  type guard = A.guard
  type solution = A.solution

  module Num = struct
    type t = NI.t -> N.t

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
end

module Make = Hashed.BijectionLevel

let%test_module _ =
  (module struct
    open Language
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

    open Specification.Builder

    let%test _ =
      let a = A.of_spec @@ constraints_only @@ [ Coincidence [ "a"; "b" ] ] in
      not (Trace.is_empty (A.gen_trace slow_strat a))
    ;;

    let%test _ =
      let a = A.of_spec @@ constraints_only [ Coincidence [ "a"; "b" ] ] in
      not (Trace.is_empty (A.gen_trace slow_strat a))
    ;;

    let%test _ =
      let a = A.of_spec @@ constraints_only [ Coincidence [ "a"; "b" ] ] in
      let trace = A.gen_trace random_strat a in
      not (Trace.is_empty trace)
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
        @@ constraints_only
             [ Coincidence [ "a"; "b" ]
             ; Exclusion { args = [ "a"; "b" ]; choice = None }
             ]
      in
      let empty2 = A.empty_sim in
      let steps = 10 in
      let trace = A.bisimulate slow_strat empty1 empty2 |> Trace.take ~steps in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Trace.length trace = steps
    ;;

    let%test _ =
      let sampling1 =
        A.of_spec
        @@ constraints_only
             [ Delay { out = "o"; arg = "i"; delay = Const 0; base = "b" } ]
      in
      let sampling2 =
        A.of_spec @@ constraints_only [ Sample { out = "o"; arg = "i"; base = "b" } ]
      in
      let steps = 10 in
      let trace = A.bisimulate random_strat sampling1 sampling2 |> Trace.take ~steps in
      (* match trace with
      | Ok l | Error l ->
        Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace l; *)
      Trace.length trace = steps
    ;;

    let%test _ =
      let a =
        A.of_spec @@ constraints_only [ Precedence { cause = "a"; conseq = "b" } ]
      in
      let trace = A.gen_trace slow_strat a |> Trace.take ~steps:10 in
      (* let g, _, _ = a in *)
      (* Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_guard (g 0.0);
      Printf.printf "%s\n" @@ Sexplib0.Sexp.to_string @@ A.sexp_of_trace trace; *)
      Trace.length trace = 10
    ;;
  end)
;;

let test_truncated a b mu sigma =
  let v = truncated_guassian_rvs ~a ~b ~mu ~sigma in
  a <= v && v <= b
;;

let%test _ =
  let _ = Random.init 12312 in
  test_truncated (-1.0) 1.0 0.0 0.5
;;
