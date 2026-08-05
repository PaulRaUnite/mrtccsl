open STS
open Def
open Syntax
open Common
open Prelude
open Number

let diff_counter_update name counter when_increase when_decrease =
  name = counter + iitec when_increase 1 0 + iitec when_decrease (-1) 0
;;

let clocks_to_bvars clocks = List.map (fun v -> binvar v) clocks

(** Builds a decision tree where only one variable can be true at the time, and has to be related to a specific [choice_var] value. *)
let build_excl_dec_tree choice_var vars =
  let rec aux level = function
    | v :: tail ->
      (* either the clock v is true and the choice variable is correct *)
      (match choice_var with
       | Some choice_var ->
         fun if_true if_false ->
           bite (choice_var == iconst level) (bite v if_true f) (!v && if_false)
       | None -> bite v)
        (* then other clocks should be false (unless it is the last condition) *)
        (if List.is_empty tail then t else !(BOr tail))
        (* or we recursively choose the next clock *)
        (aux (Int.succ level) tail)
      (* if we have exhausted clocks, then there is no solution *)
    | [] -> f
  in
  aux 0 vars
;;

let iparam_to_string = Language.Cstr.unwrap_arg ~var:Fun.id ~const:string_of_int
let rparam_to_string = Language.Cstr.unwrap_arg ~var:Fun.id ~const:Rational.to_string
let iparam_to_expr = Language.Cstr.unwrap_arg ~var:iinvar ~const:iconst
let rparam_to_expr = Language.Cstr.unwrap_arg ~var:rinvar ~const:rconst

let sample_rat_marking clock arg =
  Language.Cstr.unwrap_arg
    ~var:(fun v ->
      let sample = rpresent v in
      clock <=> sample, !sample)
    ~const:(fun _ -> t, t)
    arg
;;

let sample_int_marking clock arg =
  Language.Cstr.unwrap_arg
    ~var:(fun v ->
      let sample = ipresent v in
      clock <=> sample, !sample)
    ~const:(fun _ -> t, t)
    arg
;;

(** Stateless constraints *)

(** *)
let stateless_as_machine guard = guard |-> [] &&& t

(** Helper function that adds a range condition on integer variable (if present) and returns a stateless machine. *)
let stateless_with_range_cond len guard choice_var =
  let add_range_cond choice_var = guard && i0 <= choice_var && choice_var < iconst len in
  let guard = Option.map_or ~default:guard add_range_cond choice_var in
  stateless_as_machine guard
;;

let exclusion_as_machine clocks choice_var =
  let clocks = clocks_to_bvars clocks in
  let choice_var = Option.map iinvar choice_var in
  (* doing nothing should be still possible *)
  let guard = !(BOr clocks) || build_excl_dec_tree choice_var clocks in
  stateless_with_range_cond (List.length clocks) guard choice_var
;;

let coincidence_as_machine clocks =
  let clocks = clocks_to_bvars clocks in
  (* either all clocks are true, or all clocks are false *)
  let guard = BAnd clocks || !(BOr clocks) in
  stateless_as_machine guard
;;

let subclocking_as_machine sub super choice_var =
  let choice_var = Option.map iinvar choice_var (* x *)
  and sub = binvar sub
  and super = binvar super in
  let guard =
    match choice_var with
    | Some choice_var ->
      bite
        (* when subclock and x=0 *)
        (choice_var == i1 && sub)
        (* then super has to be present *)
        super
        (* or super might appear, but x has to be 0 *)
        (super ==> (choice_var == i0))
    | None ->
      (* when subclock then super has to be present *)
      sub ==> super
  in
  stateless_with_range_cond 2 guard choice_var
;;

let minus_as_machine out arg except =
  let out = binvar out
  and arg = binvar arg
  and except = clocks_to_bvars except in
  let guard = out <=> (arg && !(BOr except)) in
  stateless_as_machine guard
;;

let union_as_machine out args =
  assert (not (List.is_empty args));
  let out = binvar out
  and args = clocks_to_bvars args in
  let guard = out <=> BOr args in
  stateless_as_machine guard
;;

let disj_union_as_machine out args choice_var =
  assert (not (List.is_empty args));
  let out = binvar out
  and args = clocks_to_bvars args in
  let choice_var = Option.map iinvar choice_var in
  let exclusion_chain = build_excl_dec_tree choice_var args in
  let guard = bite out exclusion_chain !(BOr args) in
  stateless_with_range_cond (List.length args) guard choice_var
;;

let intersection_as_machine out args =
  assert (not (List.is_empty args));
  let out = binvar out
  and args = clocks_to_bvars args in
  let guard = out <=> BAnd args in
  stateless_as_machine guard
;;

(** Stateful constraints *)

let causality_as_machine ~strict cause conseq =
  let counter_name = Printf.sprintf "diff[%s,%s]" cause conseq in
  let counter = IStateVar counter_name in
  let cause = binvar cause
  and conseq = binvar conseq in
  bite (counter > i0) t (if strict then !conseq else conseq ==> cause)
  |-> [ diff_counter_update counter_name counter cause conseq ]
  &&& (i0 <= counter)
;;

let delay_vars out arg delay base =
  let queue_name = Printf.sprintf "iqueue[%s,%s,%s]" arg (iparam_to_string delay) base in
  let q = IQVar queue_name in
  let out = binvar out
  and arg = binvar arg
  and delay = iparam_to_expr delay
  and base = binvar base in
  queue_name, q, out, arg, delay, base
;;

(** Implements logical delay as abstract machine. Materializes [delay] {e at the moment when [arg] ticks}. *)
let delay_as_machine out arg delay base =
  let queue_name, q, out, arg, delay, base = delay_vars out arg delay base in
  let non_empty_q = ilength queue_name > i0 in
  let guard =
    BAnd
      [ (* clock [out] will happen when *)
        out
        <=> (base (* [base] ticks and *)
             && ((* there is an expired counter in the queue, or *)
                 (non_empty_q && ifirst queue_name == i0)
                 ||
                 (* [arg] and [base] ticked, and the [delay] is zero *)
                 (arg && base && delay == i0)))
      ; (* when [arg] ticks, the [delay] needs to be bigger than zero and, when queue is not empty, not smaller than the last queue element *)
        arg ==> (i0 <= delay && non_empty_q ==> (ilast queue_name <= delay))
      ]
  in
  (* push into the queue [delay] value when [arg] ticks but only if there is no same element present (instead of Boolean latch variable) *)
  let push_queue =
    iqite (arg && bite non_empty_q (ilast queue_name < delay) t) (ipush q delay) q
  in
  (* pop the queue when [out] happens and the queue is not empty *)
  let pop_queue = iqite (non_empty_q && out) (ipop push_queue) push_queue in
  (* decrease all counters in the queue when [base] happens *)
  let decrease_queue = iqite base (decrease pop_queue) pop_queue in
  guard |-> [ queue_name =| decrease_queue ] &&& t
;;

(** Implements logical delay as abstract machine. Important difference with [delay_as_machine]: checks correctness of [delay] between [out] and [arg] (in terms of [base]) {e at the moment when [out] ticks}. *)
let delay_as_late_acceptor out arg delay_arg base =
  let queue_name, q, out, arg, delay, base = delay_vars out arg delay_arg base in
  let positive_q = ilength queue_name >= i0 in
  let non_empty_q = ilength queue_name > i0 in
  let sample_delay, _ = sample_int_marking out delay_arg in
  let guard =
    bite non_empty_q (ifirst queue_name <= delay) t
    (* && i0 <= delay *)
    (* && out ==> delay_present *)
    (* clock [out] will happen when *)
    && sample_delay
    && out
       <=> (base (* [base] ticks and *)
            && bite
                 non_empty_q
                 (* if the counter in the queue is equal to the [delay], or *)
                 (ifirst queue_name == delay)
                 (* [arg] and [base] ticked, and the [delay] is zero *)
                 (arg && delay == i0))
  in
  (* push into the queue [delay] value when [arg] ticks but only if there is no same element present (instead of Boolean latch variable) *)
  let push_queue =
    iqite (arg && bite non_empty_q (ilast queue_name > i0) t) (ipush q i0) q
  in
  (* pop the queue when [out] happens and the queue is not empty *)
  let pop_queue = iqite out (ipop push_queue) push_queue in
  (* increase all counters in the queue when [base] happens*)
  let increase_queue = iqite base (increase pop_queue) pop_queue in
  guard |-> [ queue_name =| increase_queue ] &&& positive_q
;;

let alternate_as_machine first second strict =
  let switch_name = Printf.sprintf "alter[%s~%s]" first second in
  let first = binvar first
  and second = binvar second
  and switch = bsvar switch_name in
  let guard =
    if strict
    then
      (* when mode is strict, first and second has to be in different ticks: switch=false means only first could tick, same for switch=true *)
      bite switch !first !second
    else
      (* when mode is nons-trict, first and second can be in the same tick only when switch=true *)
      bite switch (first ==> second) !second
  in
  guard
  |-> [ (* switch is to be set 1 when [first] happens, 
               0 when [second] (unless at the same time as [first]), or stays as it is *)
        switch_name =& bite first t (bite second f switch)
      ]
  &&& t
;;

let sample_as_machine out arg base =
  let latch_name = Printf.sprintf "latch[%s->%s]" arg base in
  let out = binvar out
  and arg = binvar arg
  and base = binvar base
  and latch = bsvar latch_name in
  (* [out] clock ticks when there is a [base] tick and either arg already ticked before (saved in [latch]) or it ticks now. *)
  let guard = out <=> (base && (latch || arg)) in
  guard
  |-> [ (* in [latch], [base] clears the memory, [arg] is saved, otherwise [latch] is unchanged *)
        latch_name =& bite base f (latch || arg)
      ]
  &&& t
;;

let slowest_fastest_as_machine ~slowest out args =
  let counter_names = List.map (fun c -> Printf.sprintf "diff[%s, %s]" c out) args in
  let counters = List.map (fun name -> IStateVar name) counter_names in
  let out = binvar out
  and args = clocks_to_bvars args in
  let updates =
    List.zip3 args counter_names counters
    |> List.map (fun (c, name, var) -> diff_counter_update name var c out)
  in
  let guard =
    if slowest
    then (
      let disjunctions =
        List.combine args counters
        |> List.map (fun (clock, counter) -> (clock && counter == i0) || i0 < counter)
      in
      (* for [slow] tick to happen *every* clock that has zero difference with the [slow] clock has to tick *)
      out <=> BAnd disjunctions)
    else (
      let conjunctions =
        List.combine args counters
        |> List.map (fun (clock, counter) -> clock && counter == i0)
      in
      (* for [fast] tick to happen *any* clock that has zero difference with the [fast] clock has to tick *)
      out <=> BOr conjunctions)
  in
  let counter_invariants =
    if slowest
    then
      (* every clock is faster than [out], thus difference counters are at least 0 *)
      List.map (fun c -> c >= i0) counters
    else
      (* every clock is at most as fast as [out], so difference counters are at most 0 *)
      List.map (fun c -> c <= i0) counters
  in
  guard |-> updates &&& BAnd counter_invariants
;;

(* same as with the delays, error value has to be present immediately, not when [out] happens *)
let periodic_as_machine out base period error offset =
  let period_counter_name =
    Printf.sprintf
      "period[%s,%s,%s]"
      base
      (string_of_int period)
      (iparam_to_string offset)
  and nominal_name = Printf.sprintf "skip[%s]" (iparam_to_string offset) in
  let period_counter = IStateVar period_counter_name
  and out = binvar out
  and base = binvar base
  and offset = iparam_to_expr offset
  and period = IConst period
  and error = iparam_to_expr error
  and nominal = bsvar nominal_name in
  bite
    nominal
    (period_counter > i0 ==> !out || period_counter == i0 ==> (out <=> base))
    (bite (period_counter == offset) (out <=> base) !out)
  |-> [ period_counter_name
        = iite
            out
            (period + error)
            (iite
               base
               (iite nominal (period_counter - i1) (period_counter + i1))
               period_counter)
      ; nominal_name =& bite nominal t out
      ]
  &&& (i0 <= period_counter)
;;

let periodic_as_late_acceptor out base period error_arg offset_arg =
  let period_counter_name =
    Printf.sprintf
      "period[%s,%s,%s]"
      base
      (string_of_int period)
      (iparam_to_string offset_arg)
  and nominal_name = Printf.sprintf "skip[%s,%s]" base (iparam_to_string offset_arg) in
  let period_counter = IStateVar period_counter_name
  and out = binvar out
  and base = binvar base
  and offset = iparam_to_expr offset_arg
  and period_minus_one = IConst Integer.(period - 1)
  (* the period is preemptively decreased *)
  and error = iparam_to_expr error_arg
  and nominal = bsvar nominal_name in
  let sample_error, not_sample_error = sample_int_marking out error_arg
  and sample_offset, not_sample_offset = sample_int_marking out offset_arg in
  bite
    nominal
    (sample_error && not_sample_offset && (period_counter == error && base) <=> out)
    (sample_offset && not_sample_error && (period_counter == offset && base) <=> out)
  |-> [ period_counter_name
        = iite
            out
            period_minus_one
            (iite
               base
               (iite nominal (period_counter - i1) (period_counter + i1))
               period_counter)
      ; nominal_name =& bite nominal t out
      ]
  &&& (!nominal ==> (i0 <= period_counter))
;;

let first_sampled_as_machine out arg base =
  let first_name = Printf.sprintf "first[%s->%s]" arg base in
  let out = binvar out
  and arg = binvar arg
  and base = binvar base
  and first = bsvar first_name in
  bite first !out (out <=> arg) |-> [ first_name =& bite base f (bite arg t first) ] &&& t
;;

let last_sampled_as_machine out arg base =
  let last_name = Printf.sprintf "last[%s->%s]" arg base
  and latch_name = Printf.sprintf "latch[%s->%s]" arg base in
  let out = binvar out
  and arg = binvar arg
  and base = binvar base
  and last = bsvar last_name
  and latch = bsvar latch_name in
  bite
    last
    (!arg && !out)
    (out ==> arg && bite latch (base ==> out) ((arg && base) ==> out))
  |-> [ last_name =& bite base f (bite out t last)
      ; (* same as in the sample constraint *)
        latch_name =& bite base f (latch || arg)
      ]
  &&& t
;;

let forbid_as_machine left right args =
  let stack_counter_name = Printf.sprintf "diff[%s,%s]" left right in
  let left, right = binvar left, binvar right in
  let args = clocks_to_bvars args in
  let forbid_args = !(BOr args) in
  let stack = IStateVar stack_counter_name in
  let stack_update = [ diff_counter_update stack_counter_name stack left right ] in
  bite
    (stack >= i1)
    (bite (stack > i1) forbid_args (bite (right && !left) t forbid_args))
    (left ==> forbid_args && !right)
  |-> stack_update
  &&& (i0 <= stack)
;;

let allow_as_machine left right args =
  let stack_counter_name = Printf.sprintf "diff[%s,%s]" left right in
  let left, right = binvar left, binvar right in
  let args = clocks_to_bvars args in
  let forbid_args = !(BOr args) in
  let stack = IStateVar stack_counter_name in
  let stack_update = [ diff_counter_update stack_counter_name stack left right ] in
  bite
    (stack >= i1)
    (bite (stack > i1) t (bite (right && !left) forbid_args t))
    (!left ==> forbid_args && !right)
  |-> stack_update
  &&& (i0 <= stack)
;;

let mutex_as_machine open_close_pairs =
  let taken_name =
    Printf.sprintf "taken[%s]"
    @@ List.to_string ~sep:"," (Tuple.to_string2 Fun.id) open_close_pairs
  in
  let resource_name =
    Printf.sprintf "res[%s]"
    @@ List.to_string ~sep:"," (Tuple.to_string2 Fun.id) open_close_pairs
  in
  let taken = bsvar taken_name
  and resource = IStateVar resource_name in
  let pairs = List.map (Tuple.map2 binvar) open_close_pairs in
  let opens, closes = List.split pairs in
  let some_open = build_excl_dec_tree None opens in
  let some_close = build_excl_dec_tree None closes in
  let any_close = BOr closes in
  let any_open = BOr opens in
  (* let some_close = build_excl_dec_tree None closes in *)
  let update =
    [ taken_name =& bite any_open t (bite any_close f taken)
    ; resource_name
      = List.fold_lefti
          (fun e i open_v -> iite open_v (iconst i) e)
          (iite any_close i0 resource)
          opens
    ]
  in
  let match_on_resource = build_excl_dec_tree (Some resource) closes in
  bite
    taken
    ((match_on_resource || !any_close) && any_open ==> (some_open && some_close))
    ((some_open || !any_open) && !any_close)
  |-> update
  &&& (i0 <= resource && resource < iconst (List.length open_close_pairs))
;;

let rtdelay_vars out arg delay =
  let queue_name = Printf.sprintf "rqueue[%s,%s]" arg (rparam_to_string delay) in
  let out = binvar out
  and arg = binvar arg
  and delay = rparam_to_expr delay
  and queue = rqueue queue_name in
  queue_name, queue, out, arg, delay
;;

let rtdelay_as_machine ~now out arg delay =
  let queue_name, queue, out, arg, delay = rtdelay_vars out arg delay in
  let push = rqite arg (rpush queue (now +. delay)) queue in
  let pop = rqite out (rpop push) push in
  let update = [ queue_name =|. pop ] in
  bite
    (* is queue empty? *)
    (i0 < rlength queue_name)
    ((* delay is positive in non-empty queue *)
     r0 <. delay
     (* [now] cannot progress past first in the queue *)
     && now <=. rfirst queue_name
     (* force tick if [now] and first in the queue coincide *)
     && now ==. rfirst queue_name <=> out
     (* next [out] should be strictly later than already queued (as it is a logical clock) *)
     && arg ==> (rlast queue_name <. now +. delay))
    (* when queue IS empty *)
    (out <=> (arg && delay ==. r0))
  |-> update
  &&& t
;;

let rtdelay_as_late_acceptor ~now out arg delay_arg =
  let queue_name, queue, out, arg, delay = rtdelay_vars out arg delay_arg in
  let sample_delay =
    Language.Cstr.unwrap_arg
      ~var:(fun v -> out <=> rpresent v)
      ~const:(fun _ -> t)
      delay_arg
  in
  let push = rqite arg (rpush queue now) queue in
  let pop = rqite out (rpop push) push in
  let update = [ queue_name =|. pop ] in
  (sample_delay
   && bite
        (i0 < rlength queue_name)
        ((* delay is positive in non-empty queue *)
         r0 <. delay
         (* [now] cannot progress past first in the queue *)
         && now -. rfirst queue_name <=. delay
         &&
         (* force tick if [now] and first in the queue coincide *)
         now -. rfirst queue_name ==. delay <=> out)
        (out <=> (arg && delay ==. r0)))
  |-> update
  &&& t
;;

let rtperiodic_vars out period error offset =
  let last_name = Printf.sprintf "last[%s]" out in
  let out = binvar out
  and period = rconst period
  and error = rparam_to_expr error
  and offset = rparam_to_expr offset
  and last = rsvar last_name in
  last_name, last, out, period, error, offset
;;

(* TODO: add invariants to parameters, jitter periodic should have jitter no bigger than the period. *)
let drift_periodic_as_machine ~now out period error_arg offset_arg =
  let last_name, last, out, period, error, offset =
    rtperiodic_vars out period error_arg offset_arg
  in
  let sample_error =
    Language.Cstr.unwrap_arg
      ~var:(fun v -> out <=> rpresent v)
      ~const:(fun _ -> t)
      error_arg
  in
  let sample_offset =
    Language.Cstr.unwrap_arg
      ~var:(fun v -> out <=> rpresent v)
      ~const:(fun _ -> t)
      offset_arg
  in
  let update = [ last_name =. rite out now last ] in
  bite
    (last >=. r0)
    (sample_error
     (* forbid progress ahead of when [out] should occur *)
     && now -. last -. period <=. error
     (* [out] occurs precisely when [last + period + error] is *)
     && out <=> (now -. last -. period ==. error))
    (sample_offset && now <=. offset && r0 <=. offset && out <=> (now ==. offset))
  |-> update
  &&& t
;;

let jitter_periodic_as_machine ~now out period error_arg offset_arg =
  let last_name, last, out, period, error, offset =
    rtperiodic_vars out period error_arg offset_arg
  in
  let sample_error, not_sample_error = sample_rat_marking out error_arg in
  let sample_offset, not_sample_offset = sample_rat_marking out offset_arg in
  bite
    (last >=. r0)
    (sample_error
     && not_sample_offset
     (* forbid progress ahead of when [out] should occur *)
     && now -. last -. period <=. error
     (* [out] occurs precisely when [last + period + error] is *)
     && out <=> (now -. last -. period ==. error))
    (sample_offset
     && not_sample_error
     && now <=. offset
     && r0 <=. offset
     && out <=> (now ==. offset))
  |-> [ last_name =. rite out (rite (last >=. r0) (last +. period) offset) last ]
  &&& t
;;

let sporadic_as_machine ~now out at_least_arg strict =
  let last_name = Printf.sprintf "last[%s]" out in
  let out = binvar out
  and at_least = rparam_to_expr at_least_arg
  and last = rsvar last_name in
  let update = [ last_name =. rite out now last ] in
  bite
    (last >=. r0)
    ((* is [out] occurs then current time should depass previous + delay. *)
     out
     ==> if strict then at_least <. now -. last else at_least <=. now -. last)
    t
  |-> update
  &&& t
;;

(** Converts constraint into an abstract machine. *)
let of_constr now : _ Ccsl.Language.Cstr.clock_constr -> (string, string) STS.t =
  let now = rinvar now in
  function
  | Exclusion { args; choice } -> exclusion_as_machine args choice
  | Coincidence args -> coincidence_as_machine args
  | Subclocking { sub; super; choice } -> subclocking_as_machine sub super choice
  | Minus { out; arg; except } -> minus_as_machine out arg except
  | Union { out; args } -> union_as_machine out args
  | DisjunctiveUnion { out; args; choice } -> disj_union_as_machine out args choice
  | Intersection { out; args } -> intersection_as_machine out args
  | Precedence { cause; conseq } -> causality_as_machine ~strict:true cause conseq
  | Causality { cause; conseq } -> causality_as_machine ~strict:false cause conseq
  | Delay { out; arg; delay; base } -> delay_as_late_acceptor out arg delay base
  | Alternate { first; second; strict } -> alternate_as_machine first second strict
  | Sample { out; arg; base } -> sample_as_machine out arg base
  | Fastest { out; args } -> slowest_fastest_as_machine ~slowest:false out args
  | Slowest { out; args } -> slowest_fastest_as_machine ~slowest:true out args
  | FirstSampled { out; arg; base } -> first_sampled_as_machine out arg base
  | LastSampled { out; arg; base } -> last_sampled_as_machine out arg base
  | Periodic { out; base; period; error; offset } ->
    periodic_as_late_acceptor out base period error offset
  | RTdelay { out; arg; delay } -> rtdelay_as_late_acceptor ~now out arg delay
  | CumulPeriodic { out; period; error; offset } ->
    drift_periodic_as_machine ~now out period error offset
  | AbsPeriodic { out; period; error; offset } ->
    jitter_periodic_as_machine ~now out period error offset
  | Forbid { left; right; args; left_strict = false; right_strict = true } ->
    forbid_as_machine left right args
  | Allow { left; right; args; left_strict = false; right_strict = true } ->
    allow_as_machine left right args
  | Sporadic { out; at_least; strict } -> sporadic_as_machine ~now out at_least strict
  | Pool (1, open_close_pairs) -> mutex_as_machine open_close_pairs
  | Pool _ ->
    failwith "pool constraint with n > 1 is not supported in symbolic representation"
  | _ -> failwith "not implemented" (* TODO: implement the rest of the definitions *)
;;

(** Empty (as it does not constrain any clocks) machine with the basic condition of strict monotonicity on the real-time progression. *)
let empty =
  let now = "@now"
  and prev = "@prev" in
  ( now
  , { guard = rsvar prev <. rinvar now && r0 <=. rinvar now
    ; assignments = [ prev =. rinvar now ]
    ; invariant = t
    } )
;;

(** Converts numerical relation into an abstract machine. *)
let numerical_relation_as_machine
      invar
      of_param
      _marker
      comp
      (Ccsl.Language.Cstr.NumRelation (var, rel, param))
  =
  let e1 = invar var
  and e2 = of_param param in
  let guard =
    match rel with
    | `Less -> comp (e1, `Less, e2)
    | `LessEq -> comp (e1, `LessEq, e2)
    | `More -> comp (e2, `Less, e1)
    | `MoreEq -> comp (e2, `LessEq, e1)
    | `Eq -> comp (e1, `LessEq, e2) && comp (e2, `LessEq, e1)
    | `Neq -> comp (e1, `Less, e2) || comp (e2, `Less, e1)
  in
  guard |-> [] &&& t
;;

open Interpretation

module Literal = struct
  type repr = var * (var, var) t * atom_index

  (** Converts the specification constraints into a synchronized abstract machine. *)
  let of_spec ?debug:_ Language.Specification.{ clock; integer; duration; _ } : repr =
    let open STS in
    let icomp (e1, rel, e2) = BAtom (IntComp (e1, rel, e2))
    and rcomp (e1, rel, e2) = BAtom (RatComp (e1, rel, e2)) in
    let now, empty_machine = empty in
    let empty_machine = Seq.singleton empty_machine in
    let cstr_to_atom = Hashtbl.create 16 in
    let record_atom c a = Hashtbl.entry ~default:[] (List.cons a) c cstr_to_atom in
    let logical =
      Seq.map
        (fun c ->
           let m = of_constr now c in
           visit_atoms
             (record_atom
                (Language.Cstr.to_string
                   Fun.id
                   Fun.id
                   Fun.id
                   Fun.id
                   Fun.id
                   Rational.to_string
                   c))
             (* TODO: add numerical constraints too. *)
             m;
           m)
        (List.to_seq clock)
    and int_relations =
      Seq.map
        (numerical_relation_as_machine iinvar iparam_to_expr ipresent icomp)
        (List.to_seq integer)
    and rat_relations =
      Seq.map
        (numerical_relation_as_machine rinvar rparam_to_expr rpresent rcomp)
        (List.to_seq duration)
    in
    let combined_machine =
      sync_machines
        String.compare
        String.compare
        (List.of_seq
         @@ Seq.append_list [ empty_machine; logical; int_relations; rat_relations ])
    in
    now, combined_machine, cstr_to_atom
  ;;

  let step_as_inputs now Trace.{ label; time } =
    { bools = VarMap.of_seq (Seq.map (fun c -> c, true) (List.to_seq label))
    ; integers = VarMap.empty
    ; rationals = VarMap.singleton now time
    }
  ;;

  let sexp_of_step =
    Trace.sexp_of_step
      Sexplib0.Sexp_conv.(sexp_of_list sexp_of_string)
      Number.Rational.sexp_of_t
  ;;

  (** Checks if machine accepts a trace. *)
  let accept_trace (now, machine, _) trace =
    let state = default_state in
    let state =
      Seq.fold_leftr
        (fun state step ->
           let inputs = step_as_inputs now step in
           Transition.accept_transition machine state inputs)
        (Ok state)
        trace
    in
    Result.iter_error
      Transition.(
        function
        | FailedInvariant -> failwith "failed (at out) state invariant"
        | NoValidTransition -> failwith "failed (at in) state invariant"
        | _ -> ())
      state;
    Result.is_ok state
  ;;
end

module Diagram = struct
  (* TODO: generalize over label and time *)
  type trace = (bool VarMap.t, Rational.t) Trace.t

  module Acceptance = struct
    type repr = (var, var) Diagram.t * atom_index

    let of_spec ?debug:_ spec : repr =
      let now, m, index = Literal.of_spec spec in
      let diag, index = Diagram.acceptance_diagram now m index in
      diag, index
    ;;

    let transit ((d, _) : repr) state Trace.{ label; time } =
      match Diagram.accept_solution d state (label, time) with
      | Some (state, parameters) -> Ok (state, parameters)
      | None ->
        Printf.printf
          "--- step no accepted ---\ntime: %s\nclocks: %s\nstate:\n%s\n"
          (Rational.to_string time)
          (VarMap.to_string ~sep:", " Fun.id Bool.to_string label)
          (show_state state);
        Error
          ( state
          , Diagram.make_satisfaction_index
              (state_to_interface state)
              { rational =
                  (fun v ->
                    if String.equal d.now v
                    then time
                    else failwithf "requested undefined value for %s" v)
              ; integer = (fun _ -> failwith "integer inputs are not defined by trace")
              ; bool = (fun v -> VarMap.value ~default:false v label)
              }
              (* TODO: refactor into a function, probably use it in few places? *)
              d.atoms )
    ;;

    let accept_trace (r : repr) (trace : trace)
      : (state * Diagram.parameters, state * Diagram.atom_satisfaction_index) result Seq.t
      =
      let state = default_state in
      let state =
        Seq.scanr
          (fun (s, _) -> transit r s)
          (Ok (state, (VarMap.empty, VarMap.empty)))
          trace
      in
      state
    ;;

    let satisfied_by (r : repr) (trace : trace) =
      Option.map_or ~default:true Result.is_ok @@ Seq.last_opt (accept_trace r trace)
    ;;
  end

  module ParallelAcceptance = struct
    type repr = Acceptance.repr array

    module NumVarComponents = Common.Relation.Transitive.ByTag (String)

    let of_spec ?debug:_ spec : repr =
      let Language.Specification.{ clock; integer; duration; _ } = spec in
      let clock_constraints =
        List.map
          (fun c ->
             Language.Specification.
               { clock = [ c ]; integer = []; duration = []; probabilistic = [] })
          clock
      and integer_constraints =
        List.map
          (fun c ->
             Language.Specification.
               { clock = []; integer = [ c ]; duration = []; probabilistic = [] })
          integer
      and duration_constraints =
        List.map
          (fun c ->
             Language.Specification.
               { clock = []; integer = []; duration = [ c ]; probabilistic = [] })
          duration
      in
      let skip acc _ = acc in
      let save acc x = x :: acc in
      let tag spec = Language.Specification.fold skip save save save save skip [] spec in
      let constraints =
        List.append
          clock_constraints
          (List.append integer_constraints duration_constraints)
      in
      let component_index =
        List.fold_left (NumVarComponents.add ~tag) NumVarComponents.empty constraints
      in
      let components = NumVarComponents.components component_index in
      let components =
        Seq.map Language.Specification.(List.fold_left merge empty) components
      in
      let diagrams =
        Seq.map
          (fun spec ->
             let now, m, index = Literal.of_spec spec in
             let diag, index = Diagram.acceptance_diagram now m index in
             diag, index)
          components
      in
      Array.of_seq diagrams
    ;;

    let accept_trace (acceptors : repr) (trace : trace)
      : ( state array * Diagram.parameters
          , (state * Diagram.atom_satisfaction_index option) array )
          result
          Seq.t
      =
      let states = Array.init (Array.length acceptors) (fun _ -> default_state) in
      let combine _ _ _ =
        failwith
          "ParallelAcceptance.accept_trace: not possible to have 2 parameter derivations"
      in
      Seq.scanr
        (fun (states, _) step ->
           let results =
             Array.map2 (fun r s -> Acceptance.transit r s step) acceptors states
           in
           let all_ok = Array.for_all Result.is_ok results in
           if all_ok
           then (
             let params, states =
               Array.fold_left_map
                 (fun (pints, prats) -> function
                    | Ok (state, (ints, rats)) ->
                      ( (VarMap.union combine pints ints, VarMap.union combine prats rats)
                      , state )
                    | Error _ -> failwith "all results are ok, should not be possible")
                 (VarMap.empty, VarMap.empty)
                 results
             in
             Ok (states, params))
           else
             Error
               (Array.map
                  (function
                    | Ok (state, _) -> state, None
                    | Error (state, index) -> state, Some index)
                  results))
        (Ok (states, (VarMap.empty, VarMap.empty)))
        trace
    ;;

    let satisfied_by (r : repr) (trace : trace) =
      Option.map_or ~default:true Result.is_ok @@ Seq.last_opt (accept_trace r trace)
    ;;
  end

  module Simulation = struct
    module RI = Interval.Make (Rational)

    module II = struct
      include Interval.Make (Integer)

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

    type repr = (var, var) Diagram.sim_repr * atom_index

    let discr_dist_value ratios interval =
      let open Stdlib in
      let left, right = II.to_nonstrict interval in
      let available =
        List.filter (fun (value, _) -> left <= value && value <= right) ratios
      in
      let sum = List.fold_left (fun acc (_, ratio) -> acc + ratio) 0 available in
      let rvs () =
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
      in
      Diagram.make_gen 0 rvs
    ;;

    (* TODO: refactor this bulshit, this needs to be unified with the native backend *)
    let cont_dist_value dist cond =
      let open Language.Cstr in
      let open Number in
      let rvs =
        match dist with
        | Uniform ->
          let lower, upper =
            Option.unwrap
              ~expect:"uniform distribution is undefined on exclusive intervals"
            @@ RI.constant_bounds cond
          in
          fun () -> Rational.random lower upper
        | Normal { mean; deviation } ->
          let mu = Rational.to_float mean in
          let sigma = Rational.to_float deviation in
          let bounds =
            Option.unwrap ~expect:"gaussian distribution is undefined on exclusive bounds"
            @@ RI.constant_bounds cond
          in
          let a, b = Tuple.map2 Rational.to_float bounds in
          fun () ->
            let sample = Float.truncated_guassian_rvs ~a ~b ~mu ~sigma in
            Rational.of_float sample
        | Exponential { rate } ->
          let rate = Rational.to_float rate in
          (match RI.constant_bounds cond with
           | None -> fun () -> Rational.of_float @@ Float.exponential_rvs ~rate
           | Some bounds ->
             let a, b = Tuple.map2 Rational.to_float bounds in
             fun () -> Rational.of_float @@ Float.truncated_exponential_rvs ~a ~b ~rate)
      in
      Diagram.make_gen Rational.zero rvs
    ;;

    let sim_of_spec ?debug:_ ?(instances = 1) spec : repr list =
      let now, m, index =
        Literal.of_spec { spec with integer = []; duration = []; probabilistic = [] }
      in
      let clocks = List.sort_uniq String.compare @@ Language.Specification.clocks spec in
      let duration_bounds =
        Language.Specification.(spec.duration)
        |> List.map (function
          | Language.Cstr.NumRelation (v, rel, Const c) -> v, RI.of_rel rel c
          | _ -> failwith "uncertainty relations between variables are not supported")
        |> List.fold_left
             (fun acc (v, rel) -> VarMap.entry ~default:rel (RI.inter rel) v acc)
             VarMap.empty
      and integer_bounds =
        Language.Specification.(spec.integer)
        |> List.map (function
          | Language.Cstr.NumRelation (v, rel, Const c) -> v, II.of_rel rel c
          | _ -> failwith "uncertainty relations between variables are not supported")
        |> List.fold_left
             (fun acc (v, rel) -> VarMap.entry ~default:rel (II.inter rel) v acc)
             VarMap.empty
      in
      let diag, index = Diagram.simulation_diagram now m clocks index in
      List.init instances (fun _ ->
        let int_gens, rat_gens =
          List.partition_map
            Language.Cstr.(
              function
              | DiscreteValued { name; ratios } ->
                Either.Left
                  (name, discr_dist_value ratios (VarMap.find name integer_bounds))
              | ContinuousValued { name; dist } ->
                Either.Right
                  (name, cont_dist_value dist (VarMap.find name duration_bounds)))
            spec.probabilistic
        in
        let int_gens = VarMap.of_list int_gens
        and rat_gens = VarMap.of_list rat_gens in
        let int_gens =
          VarMap.merge
            (fun _ gen bound ->
               match gen, bound with
               | Some gen, _ -> Some gen
               | _, Some bound ->
                 let l, r =
                   Option.unwrap ~expect:"bounds have to be defined for integer variables"
                   @@ II.constant_bounds bound
                 in
                 let open Stdlib in
                 let ratios = List.init (r - l + 1) (fun i -> i + l, 1) in
                 Some (discr_dist_value ratios bound)
               | _ -> failwith "unreachable")
            int_gens
            integer_bounds
        and rat_gens =
          VarMap.merge
            (fun _ gen bound ->
               match gen, bound with
               | Some gen, _ -> Some gen
               | _, Some bound -> Some (cont_dist_value Uniform bound)
               | _ -> failwith "unreachable")
            rat_gens
            duration_bounds
        in
        ( Diagram.{ diagram = diag; rat_gens; int_gens; clocks = Array.of_list clocks }
        , index ))
    ;;

    let gen_trace time_strategy (repr, _) : trace =
      let state = default_state in
      Seq.unfold
        (fun state ->
           match Diagram.gen_step time_strategy repr state with
           | Some (state, (label, time)) -> Some (Trace.{ label; time }, state)
           | None ->
             Printf.printf
               "generation stopped in state %s\nint params: %s\nrat params: %s\n"
               (show_state state)
               (VarMap.to_string
                  Fun.id
                  (fun g -> Integer.to_string Diagram.(g.value))
                  repr.int_gens)
               (VarMap.to_string
                  Fun.id
                  (fun g -> Rational.to_string Diagram.(g.value))
                  repr.rat_gens);
             None)
        state
    ;;
  end
end
