open Symbolic.Machine
open Syntax
open Prelude
open Number

let diff_counter_update name counter when_increase when_decrease =
  name = counter + iitec when_increase 1 0 + iitec when_decrease (-1) 0
;;

let clocks_to_bvars clocks = List.map (fun v -> BInputVar v) clocks

(** Builds a decision tree where only one variable can be true at the time, and has to be related to a specific [choice_var] value. *)
let build_excl_dec_tree choice_var vars =
  let rec aux level = function
    | v :: tail ->
      bite
        (* either the clock v is true and the choice variable is correct *)
        (match choice_var with
         | Some choice_var -> choice_var == iconst level && v
         | None -> v)
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

(** Stateless constraints *)

(** *)
let stateless_as_machine guard = [ t @@@ guard |-> [] ] &&& t

(** Helper function that adds a range condition on integer varaible (if present) and returns stateless machine. *)
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
  and sub = BInputVar sub
  and super = BInputVar super in
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
  let out = BInputVar out
  and arg = BInputVar arg
  and except = clocks_to_bvars except in
  let guard = out <=> (arg && !(BOr except)) in
  stateless_as_machine guard
;;

let union_as_machine out args =
  assert (not (List.is_empty args));
  let out = BInputVar out
  and args = clocks_to_bvars args in
  let guard = out <=> BOr args in
  stateless_as_machine guard
;;

let disj_union_as_machine out args choice_var =
  assert (not (List.is_empty args));
  let out = BInputVar out
  and args = clocks_to_bvars args in
  let choice_var = Option.map iinvar choice_var in
  let exclusion_chain = build_excl_dec_tree choice_var args in
  let guard = bite out exclusion_chain !(BOr args) in
  stateless_with_range_cond (List.length args) guard choice_var
;;

let intersection_as_machine out args =
  assert (not (List.is_empty args));
  let out = BInputVar out
  and args = clocks_to_bvars args in
  let guard = out <=> BAnd args in
  stateless_as_machine guard
;;

(** Stateful constraints *)

let causality_as_machine ~strict cause conseq =
  let counter_name = Printf.sprintf "diff[%s,%s]" cause conseq in
  let counter = IStateVar counter_name in
  let cause = BInputVar cause
  and conseq = BInputVar conseq in
  [ (* c>0 : no restriction on clocks *)
    (counter > i0) @@@ t |-> [ diff_counter_update counter_name counter cause conseq ]
  ; (* c=0 : when strict, only cause can happen, when non-strict, consequence cannot happen on its own *)
    ((counter == i0) @@@ if strict then !conseq else conseq ==> cause)
    |-> [ diff_counter_update counter_name counter cause conseq ]
  ]
  &&& (i0 <= counter)
;;

let delay_vars out arg delay base =
  let queue_name = Printf.sprintf "iqueue[%s,%s,%s]" arg (iparam_to_string delay) base in
  let q = IQVar queue_name in
  let out = BInputVar out
  and arg = BInputVar arg
  and delay = iparam_to_expr delay
  and base = BInputVar base in
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
  [ t @@@ guard |-> [ queue_name =| decrease_queue ] ] &&& t
;;

(** Implements logical delay as abstract machine. Important difference with [delay_as_machine]: checks correctness of [delay] between [out] and [arg] (in terms of [base]) {e at the moment when [out] ticks}. *)
let delay_as_late_acceptor out arg delay base =
  let queue_name, q, out, arg, delay, base = delay_vars out arg delay base in
  let positive_q = ilength queue_name >= i0 in
  let non_empty_q = ilength queue_name > i0 in
  let guard =
    bite non_empty_q (ifirst queue_name <= delay) t
    && i0 <= delay
    &&
    (* clock [out] will happen when *)
    out
    <=> (base (* [base] ticks and *)
         && bite
              non_empty_q
              (* if the counter in the queue is equal to the [delay], or *)
              (ifirst queue_name == delay && i0 < delay)
              (* [arg] and [base] ticked, and the [delay] is zero *)
              (arg && delay == i0))
  in
  (* push into the queue [delay] value when [arg] ticks but only if there is no same element present (instead of Boolean latch variable) *)
  let push_queue =
    iqite (arg && bite non_empty_q (ilast queue_name > i0) t) (ipush q i0) q
  in
  (* pop the queue when [out] happens and the queue is not empty *)
  let pop_queue = iqite out (ipop push_queue) push_queue in
  (* increase all counters in the queue [base] happens*)
  let increase_queue = iqite base (increase pop_queue) pop_queue in
  [ t @@@ guard |-> [ queue_name =| increase_queue ] ] &&& positive_q
;;

let alternate_as_machine first second strict =
  let switch_name = Printf.sprintf "alter[%s~%s]" first second in
  let first = BInputVar first
  and second = BInputVar second
  and switch = BStateVar switch_name in
  let guard =
    if strict
    then
      (* when mode is strict, first and second has to be in different ticks: switch=false means only first could tick, same for switch=true *)
      bite switch !first !second
    else
      (* when mode is nons-trict, first and second can be in the same tick only when switch=true *)
      bite switch (first ==> second) !second
  in
  [ t @@@ guard
    |-> [ (* switch is to be set 1 when [first] happens, 
               0 when [second] (unless at the same time as [first]), or stays as it is *)
          switch_name =& bite first t (bite second f switch)
        ]
  ]
  &&& t
;;

let sample_as_machine out arg base =
  let latch_name = Printf.sprintf "latch[%s->%s]" arg base in
  let out = BInputVar out
  and arg = BInputVar arg
  and base = BInputVar base
  and latch = BStateVar latch_name in
  (* [out] clock ticks when there is a [base] tick and either arg already ticked before (saved in [latch]) or it ticks now. *)
  let guard = out <=> (base && (latch || arg)) in
  [ t @@@ guard
    |-> [ (* in [latch], [out] clears the memory, [arg] is saved, otherwise [latch] is unchanged *)
          latch_name =& bite out f (latch || arg)
        ]
  ]
  &&& t
;;

let slowest_fastest_as_machine ~slowest out args =
  let counter_names = List.map (fun c -> Printf.sprintf "diff[%s, %s]" c out) args in
  let counters = List.map (fun name -> IStateVar name) counter_names in
  let out = BInputVar out
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
  [ t @@@ guard |-> updates ] &&& BAnd counter_invariants
;;

let periodic_as_machine out base period error offset =
  let period_counter_name =
    Printf.sprintf
      "period[%s,%s,%s]"
      base
      (string_of_int period)
      (iparam_to_string offset)
  and nominal_name = Printf.sprintf "skip[%s]" (iparam_to_string offset) in
  let period_counter = IStateVar period_counter_name
  and out = BInputVar out
  and base = BInputVar base
  and offset = iparam_to_expr offset
  and period = IConst period
  and error = iparam_to_expr error
  and nominal = BStateVar nominal_name in
  [ !nominal
    @@@ (period_counter < offset ==> !out || period_counter == offset ==> (out <=> base))
    |-> [ period_counter_name = iite out (period + error) (period_counter + i1)
        ; nominal_name =& (period_counter == offset)
        ]
  ; nominal @@@ (period_counter > i0 ==> !out || period_counter == i0 ==> (out <=> base))
    |-> [ period_counter_name = iite out (period + error) (period_counter - i1)
        ; nominal_name =& t
        ]
  ]
  &&& (i0 <= period_counter)
;;

let first_sampled_as_machine out arg base =
  let first_name = Printf.sprintf "first[%s->%s]" arg base in
  let out = BInputVar out
  and arg = BInputVar arg
  and base = BInputVar base
  and first = BStateVar first_name in
  [ t @@@ bite first !out (out <=> arg)
    |-> [ first_name =& bite base f (bite out t first) ]
  ]
  &&& t
;;

let last_sampled_as_machine out arg base =
  let last_name = Printf.sprintf "last[%s->%s]" arg base in
  let out = BInputVar out
  and arg = BInputVar arg
  and base = BInputVar base
  and last = BStateVar last_name in
  [ t @@@ bite last (!arg && !out) (out ==> arg)
    |-> [ last_name =& bite base f (bite out t last) ]
  ]
  &&& t
;;

let forbid_as_machine left right args =
  let stack_counter_name = Printf.sprintf "diff[%s,%s]" left right in
  let left, right = BInputVar left, BInputVar right in
  let args = clocks_to_bvars args in
  let forbid_args = !(BOr args) in
  let stack = IStateVar stack_counter_name in
  let stack_update = [ diff_counter_update stack_counter_name stack left right ] in
  [ (stack == i0) @@@ (left ==> forbid_args) |-> stack_update
  ; (stack == i1) @@@ bite (right && !left) t forbid_args |-> stack_update
  ; (stack > i1) @@@ forbid_args |-> stack_update
  ]
  &&& (i0 <= stack)
;;

let allow_as_machine left right args =
  let stack_counter_name = Printf.sprintf "diff[%s,%s]" left right in
  let left, right = BInputVar left, BInputVar right in
  let args = clocks_to_bvars args in
  let forbid_args = !(BOr args) in
  let stack = IStateVar stack_counter_name in
  let stack_update = [ diff_counter_update stack_counter_name stack left right ] in
  [ (stack == i0) @@@ (!left ==> forbid_args) |-> stack_update
  ; (stack == i1) @@@ bite (right && !left) forbid_args t |-> stack_update
  ; (stack > i1) @@@ t |-> stack_update
  ]
  &&& (i0 <= stack)
;;

let mutex_as_machine open_close_pairs =
  let free_name =
    Printf.sprintf "free[%s]"
    @@ List.to_string ~sep:"," (Tuple.to_string2 Fun.id) open_close_pairs
  in
  let resource_name =
    Printf.sprintf "res[%s]"
    @@ List.to_string ~sep:"," (Tuple.to_string2 Fun.id) open_close_pairs
  in
  let free = BStateVar free_name
  and resource = IStateVar resource_name in
  let pairs = List.map (Tuple.map2 binvar) open_close_pairs in
  let opens, closes = List.split pairs in
  let any_open = BOr opens in
  let any_close = BOr closes in
  let update =
    [ free_name =& bite any_open t (bite any_close f free)
    ; resource_name
      = iite
          any_open
          (List.reduce_left
             ( + )
             Fun.id
             (List.mapi (fun i open_v -> iite open_v (iconst i) i0) opens))
          i0
    ]
  in
  let match_on_resource = build_excl_dec_tree (Some resource) closes in
  [ free @@@ (any_open && !any_close) |-> update
  ; !free @@@ ((match_on_resource || !any_close) && any_open ==> any_close) |-> update
  ]
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
  [ (i0 == rlength queue_name) @@@ (out <=> (arg && delay ==. r0)) |-> update
  ; (i0 < rlength queue_name)
    @@@ ((* delay is positive in non-empty queue *)
         r0 <. delay
         (* [now] cannot progress past first in the queue *)
         && now <=. rfirst queue_name
         (* force tick if [now] and first in the queue coincide *)
         && now ==. rfirst queue_name <=> out
         (* next [out] should be strictly later than already queued (as it is a logical clock) *)
         && arg ==> (rlast queue_name <. now +. delay))
    |-> update
  ]
  &&& t
;;

(* TODO: another way to do acceptance is to capture symbolic value of the variable as entrace and check satisfaction when out.*)

let rtdelay_as_late_acceptor ~now out arg delay =
  let queue_name, queue, out, arg, delay = rtdelay_vars out arg delay in
  let push = rqite arg (rpush queue now) queue in
  let pop = rqite out (rpop push) push in
  let update = [ queue_name =|. pop ] in
  [ (i0 == rlength queue_name) @@@ (out <=> (arg && delay ==. r0)) |-> update
  ; (i0 < rlength queue_name)
    @@@ ((* delay is positive in non-empty queue *)
         r0 <. delay
         (* [now] cannot progress past first in the queue *)
         && now <=. rfirst queue_name +. delay
         (* force tick if [now] and first in the queue coincide *)
         && now -. rfirst queue_name ==. delay <=> out)
    |-> update
  ]
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

let drift_periodic_as_machine ~now out period error offset =
  let last_name, last, out, period, error, offset =
    rtperiodic_vars out period error offset
  in
  let next_out = last +. period +. error in
  let update = [ last_name =. rite out now last ] in
  [ (last <. r0) @@@ (now <=. offset && r0 <=. offset && out <=> (now ==. offset))
    |-> update
  ; (last >=. r0)
    @@@ ((* forbid progress ahead of when [out] should occur *)
         now <=. next_out
         (* [out] occurs precisely when [last + period + error] is *)
         && out <=> (next_out ==. now))
    |-> update
  ]
  &&& t
;;

let jitter_periodic_as_machine ~now out period error offset =
  let last_name = Printf.sprintf "last[%s]" out in
  let out = binvar out
  and period = rconst period
  and error = rparam_to_expr error
  and offset = rparam_to_expr offset
  and last = rsvar last_name in
  let next_out = last +. period +. error in
  [ (last <. r0) @@@ (now <=. offset && r0 <=. offset && out <=> (now ==. offset))
    |-> [ last_name =. rite out offset last ]
  ; (last >=. r0)
    @@@ ((* forbid progress ahead of when [out] should occur *)
         now <=. next_out
         (* [out] occurs precisely when [last + period + error] is *)
         && out <=> (next_out ==. now))
    |-> [ last_name =. rite out (last +. period) last ]
  ]
  &&& t
;;

(* TODO: sporadic seems to lost its purpose, it is sort of periodic with arbitrary offset. *)
let sporadic_as_machine ~now out at_least =
  let last_name = Printf.sprintf "last[%s]" out in
  let out = binvar out
  and at_least = rparam_to_expr at_least
  and last = rsvar last_name in
  let update = [ last_name =. rite out now last ] in
  [ (last <. r0) @@@ t |-> update
  ; (last >=. r0)
    @@@ ((* forbid progress ahead of when [out] should occur *)
         now <=. last +. at_least
         (* [out] occurs precisely *)
         && out <=> (last +. at_least ==. now))
    |-> update
  ]
  &&& t
;;

(** Converts constraint into an abstract machine. *)
let constraint_as_machine now
  : _ Ccsl.Language.Cstr.clock_constr -> (string, string) Symbolic.Machine.t
  =
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
    periodic_as_machine out base period error offset
  | RTdelay { out; arg; delay } -> rtdelay_as_late_acceptor ~now out arg delay
  | CumulPeriodic { out; period; error; offset } ->
    drift_periodic_as_machine ~now out period error offset
  | AbsPeriodic { out; period; error; offset } ->
    jitter_periodic_as_machine ~now out period error offset
  | Forbid { left; right; args } -> forbid_as_machine left right args
  | Allow { left; right; args } -> allow_as_machine left right args
  | Sporadic { out; at_least } -> sporadic_as_machine ~now out at_least
  | Pool (1, open_close_pairs) -> mutex_as_machine open_close_pairs
  | Pool _ ->
    failwith "pool constraint with n > 1 is not supported in symbolic representation"
;;

(** Empty (as it does not constrain any clocks) machine with the basic condition of strict monotonicity on the real-time progression. *)
let empty =
  let now = "@now"
  and prev = "@prev" in
  ( now
  , { transitions =
        [ t @@@ (rsvar prev <. rinvar now && r0 <=. rinvar now) |-> [ prev =. rinvar now ]
        ]
    ; invariant = t
    } )
;;

(** Converts numerical relation into an abstract machine. *)
let numerical_relation_as_machine
      invar
      of_param
      comp
      (Ccsl.Language.Cstr.NumRelation (var, rel, param))
  =
  let e1 = invar var
  and e2 = of_param param in
  [ t @@@ comp (e1, rel, e2) |-> [] ] &&& t
;;

open Interpretation

type sim = var * (var, var) t

(** Converts the specification constraints into a synchronized abstract machine. *)
let of_spec ?debug:_ Language.Specification.{ clock; integer; duration; _ } : sim =
  let open Symbolic.Machine in
  let icomp (e1, rel, e2) = IntComp (e1, rel, e2)
  and rcomp (e1, rel, e2) = RatComp (e1, rel, e2) in
  let now, empty_machine = empty in
  let logical = Seq.map (constraint_as_machine now) (List.to_seq clock)
  and int_relations =
    Seq.map
      (numerical_relation_as_machine iinvar iparam_to_expr icomp)
      (List.to_seq integer)
  and rat_relations =
    Seq.map
      (numerical_relation_as_machine rinvar rparam_to_expr rcomp)
      (List.to_seq duration)
  in
  let combined_machine =
    Seq.fold_left
      sync_machines
      empty_machine
      (Seq.append_list [ logical; int_relations; rat_relations ])
  in
  now, combined_machine
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
let accept_trace (now, machine) trace =
  let state = default_state in
  let state =
    Seq.fold_leftr
      (fun state step ->
         let inputs = step_as_inputs now step in
         accept_transition machine state inputs)
      (Ok state)
      trace
  in
  Result.is_ok state
;;
