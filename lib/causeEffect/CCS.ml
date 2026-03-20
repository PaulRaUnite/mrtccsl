(** Calculus of communicating systems. *)

open Common
open Prelude
open Ppx_compare_lib.Builtin

type 'v vector = 'v Iarray.t

type ('c, 'r) expr =
  | Defined of 'c
  | Ref of 'r

type local_value = LocalValue of int [@@deriving compare]
type 'v value_expr = ('v, local_value) expr

(** Action type. *)
type ('e, 'v) action =
  | Send of 'e * 'v (** Send action. *)
  | Receive of 'e * local_value (** Receive action. *)
  | Tau (** Tau represents unobservable action. *)
[@@deriving compare]

let event_opt = function
  | Send (e, _) | Receive (e, _) -> Some e
  | Tau -> None
;;

(** Inverts send and receive. Tau cannot be changed. *)
let invert_action = function
  | Send (e, v) -> Receive (e, v)
  | Receive (e, v) -> Send (e, v)
  | Tau -> Tau
;;

(** Universally quantified function on events. *)
type ('tname, 'c) closure = { call : 'e 'v. 'e vector -> ('tname, 'e, 'v, 'c) process }

(** Process type. *)
and ('tname, 'e, 'v, 'c) process =
  | Nil (** End of process. *)
  | Prefix of ('e, 'v value_expr) action * 'p (** Action followed by process. *)
  | Parallel of 'p list (** Parallel pair of processes. *)
  | Choice of 'p list (** Choice between the processes. *)
  | Restrict of 'e vector * 'p
  (** Introduction of action/hiding an action. Essentially creates an anonymous action. *)
  | TemplateCall of 'tname * 'e vector * 'v value_expr vector
  (** Replaces variables in value places in a process with value parameters. *)
  | Closure of (('tname, 'c) closure * 'e vector)
  | ComputeValue of local_value * ('c vector -> 'c) * 'v value_expr vector * 'p
  constraint 'p = ('tname, 'e, 'v, 'c) process

type arg_event = ArgEvent of int
type arg_value = ArgValue of int
type 'v inline_value = InlineValue of 'v

type ('tname, 'v) template =
  ('tname, arg_event, ('v inline_value, arg_value) expr, 'v) process

type ('tname, 'v) lib = ('tname * ('tname, 'v) template) list
type ('tname, 'event, 'v) system = ('tname, 'v) lib * ('tname, 'event, 'v, 'v) process

let map_action ~event_f ~value_f = function
  | Send (e, v) -> Send (event_f e, value_f v)
  | Receive (e, var) -> Receive (event_f e, var)
  | Tau -> Tau
;;

let map_expr ~def_f ~ref_f = function
  | Defined c -> Defined (def_f c)
  | Ref v -> Ref (ref_f v)
;;

let map_value_expr ~const_f = map_expr ~def_f:const_f ~ref_f:Fun.id
let ref v = Ref v
let def v = Defined v

let rec instantiate action_args value_args (p : ('n, 'v) template)
  : ('n, 'e, 'v, 'v) process
  =
  let event_f (ArgEvent i) = Iarray.get action_args i in
  let value_f = function
    | Defined (Ref (ArgValue i)) -> Defined (Iarray.get value_args i)
    | Defined (Defined (InlineValue v)) -> Defined v
    | Ref local -> Ref local
  in
  match p with
  | Nil -> Nil
  | Prefix (a, p) ->
    let a = map_action ~event_f ~value_f a in
    Prefix (a, instantiate action_args value_args p)
  | Parallel ps -> Parallel (List.map (instantiate action_args value_args) ps)
  | Choice ps -> Choice (List.map (instantiate action_args value_args) ps)
  | Restrict (local_events, p) ->
    let local_events = Iarray.map event_f local_events in
    let p = instantiate action_args value_args p in
    Restrict (local_events, p)
  | TemplateCall (name, action_refs, value_exprs) ->
    let action_refs = Iarray.map event_f action_refs in
    let value_exprs = Iarray.map value_f value_exprs in
    TemplateCall (name, action_refs, value_exprs)
  | Closure (c, args) ->
    let args = Iarray.map event_f args in
    Closure (c, args)
  | ComputeValue (var, f, args, p) ->
    let args = Iarray.map value_f args in
    ComputeValue (var, f, args, instantiate action_args value_args p)
;;

module Syntax = struct
  let nil = Nil
  let[@inline always] ( @! ) (e, v) p = Prefix (Send (e, v), p)
  let[@inline always] ( @? ) (e, v) p = Prefix (Receive (e, v), p)
  let[@inline always] ( + ) p1 p2 = Choice [ p1; p2 ]
  let[@inline always] ( || ) p1 p2 = Parallel [ p1; p2 ]
  let[@inline always] call name actions values = TemplateCall (name, actions, values)
  let[@inline always] nu e p = Restrict (e, p)
end

module PP = struct end

module Standard = struct
  open Syntax

  (** 
  Queue process of max size 2, recursively defined as:
   {math \begin{aligned}
    Q_2(in, out) &= in(x).Q1(in, out) \langle x \rangle \\
    Q_1(in, out)\langle a_0 \rangle &= in(x).Q_0(in, out)\langle x, a_0 \rangle + \overline{out}\langle a_0 \rangle.Q_2(in, out)\\
    Q_0(in, out)\langle a_0, a_1 \rangle &= \overline{out}\langle a_1 \rangle.Q_1(in, out)\langle a_0 \rangle
\end{aligned} } *)
  let queue2_templates (type a) () : (string, a) lib =
    let input = ArgEvent 0
    and output = ArgEvent 1 in
    let x = LocalValue 0 in
    let varg0 = Ref (ArgValue 0)
    and varg1 = Ref (ArgValue 1) in
    let q2 = (input, x) @? call "Q_1" [| input; output |] [| Ref x |] in
    let q11 = (input, x) @? call "Q_0" [| input; output |] [| Ref x; Defined varg0 |]
    and q12 = (output, Defined varg0) @! call "Q_2" [| input; output |] [||] in
    let q1 = q11 + q12 in
    let q0 =
      (output, Defined varg1) @! call "Q_1" [| input; output |] [| Defined varg0 |]
    in
    [ "Q_2", q2; "Q_1", q1; "Q_0", q0 ]
  ;;

  let queue2 (type e) (type c) input output : (string, e, c) system =
    queue2_templates (), call "Q_0" [| input; output |] [||]
  ;;

  (**
  Unbounded queue template, defined as:
  {math 
    \begin{aligned}
      R(in,out) &= in (x). \overline{out}\langle x \rangle . R(in,out) \\
      Q(in,out) &= in(x). (\nu c) \left( \overline{out}\langle x \rangle . R(c,out) \parallel Q(in, c)\right)
    \end{aligned}
  }
  *)
  let queue_template (type a) () : (string, a) lib =
    let input = ArgEvent 0
    and output = ArgEvent 1
    and c = ArgEvent 2 in
    let x = LocalValue 0 in
    let r = (input, x) @? (output, Ref x) @! call "R" [| input; output |] [||] in
    let q =
      (input, x)
      @? nu
           [| c |]
           (((output, Ref x) @! call "R" [| c; output |] [||])
            || call "Q" [| input; c; output |] [||])
    in
    [ "Q", q; "R", r ]
  ;;

  let queue write read anon : _ system = queue_template (), call "Q" [| write; read; anon |] [||]

  (**
  Variable defined as:
  {math V(w,r)\langle v \rangle = w(x). V(w,r)\langle x \rangle + \overline{r}\langle v \rangle . V(w,r)\langle v \rangle }
  *)
  let var_template () : (string, 'a) lib =
    let warg = ArgEvent 0
    and rarg = ArgEvent 1 in
    let varg0 = Ref (ArgValue 0) in
    let x = LocalValue 0 in
    let w = (warg, x) @? call "V" [| warg; rarg |] [| Ref x |]
    and r = (rarg, Defined varg0) @! call "V" [| warg; rarg |] [| Defined varg0 |] in
    [ "V", w + r ]
  ;;

  let variable write read initial : _ system =
    var_template (), call "V" [| write; read |] [| Defined initial |]
  ;;
end

open Common

module type Event = sig
  include Interface.TotalOrder

  val anon : t -> int -> t
end

module type Variable = sig
  include Interface.TotalOrder
end

module DefaultVariable (V : Interface.TotalOrder) = struct
  type t =
    | Explicit of V.t
    | Anon of int
  [@@deriving compare]

  let to_string v = Printf.sprintf "anon.%i" v
  let explicit v = Explicit v
  let anon index = Anon index
end

module Semantics (T : Interface.TotalOrder) (E : Event) = struct
  module Templates = Map.Make (T)

  let unwrap_value_expr = function
    | Defined c -> c
    | Ref (LocalValue v) -> failwithf "bound variable %i was not instantiated" v
  ;;

  let rec define_var variable value =
    let map_value = function
      | Defined c -> Defined c
      | Ref lv -> if lv = variable then Defined value else Ref lv
    in
    function
    | Nil -> Nil
    | Prefix (Send (e, v), p) -> Prefix (Send (e, map_value v), p)
    | Prefix (a, p) -> Prefix (a, define_var variable value p)
    | Parallel ps -> Parallel (List.map (define_var variable value) ps)
    | Choice ps -> Choice (List.map (define_var variable value) ps)
    | Restrict (local_events, p) -> Restrict (local_events, define_var variable value p)
    | TemplateCall (name, events, values) ->
      let values = Iarray.map map_value values in
      TemplateCall (name, events, values)
    | Closure (c, args) -> Closure (c, args)
    | ComputeValue (var, f, args, p) ->
      let args = Iarray.map map_value args in
      ComputeValue (var, f, args, p)
  ;;

  let rec unroll ~lib = function
    | Nil -> Nil
    | Prefix _ as p -> p
    | Parallel processes ->
      let unrolled = List.flat_map (unroll_parallel ~lib) processes in
      (match unrolled with
       | [ p ] -> p
       | [] -> Nil
       | processes -> Parallel processes)
    | Choice processes ->
      let unrolled = List.flat_map (unroll_choice ~lib) processes in
      (match unrolled with
       | [ p ] -> p
       | [] -> Nil
       | processes -> Parallel processes)
    | Restrict (_, Nil) -> Nil
    | Restrict _ as p -> p
    | TemplateCall (name, actions, values) ->
      let const_args = Iarray.map unwrap_value_expr values in
      let p = Templates.find name lib in
      unroll ~lib (instantiate actions const_args p)
    | Closure (c, args) -> unroll ~lib (c.call args)
    | ComputeValue (var, f, args, p) ->
      let value = f (Iarray.map unwrap_value_expr args) in
      let p = define_var var value p in
      unroll ~lib p

  and unroll_parallel ~lib = function
    | Nil -> []
    | Parallel processes -> List.flat_map (unroll_parallel ~lib) processes
    | p -> [ unroll ~lib p ]

  and unroll_choice ~lib = function
    | Choice processes -> List.flat_map (unroll_choice ~lib) processes
    | p -> [ p ]
  ;;

  module Events = Set.Make (E)
  module EventMap = Map.Make (E)

  let rec refactor_restrict_list count map set ps =
    List.fold_left
      (fun (count, map, set, list) p ->
         let nc, nm, ns, np = refactor_restrict count map set p in
         nc, nm, ns, np :: list)
      (count, map, set, [])
      ps

  and refactor_restrict count map set p =
    let event_f e = Option.value ~default:e @@ EventMap.find_opt e map in
    match p with
    | Nil -> count, map, set, Nil
    | Prefix (a, p) ->
      let a = map_action ~event_f ~value_f:Fun.id a in
      let count, map, set, p = refactor_restrict count map set p in
      count, map, set, Prefix (a, p)
    | Parallel ps ->
      let count, map, set, ps = refactor_restrict_list count map set ps in
      count, map, set, Parallel ps
    | Choice ps ->
      let count, map, set, ps = refactor_restrict_list count map set ps in
      count, map, set, Choice ps
    | TemplateCall (name, events, values) ->
      let events = Iarray.map event_f events in
      count, map, set, TemplateCall (name, events, values)
    | Closure (c, events) ->
      let events = Iarray.map event_f events in
      count, map, set, Closure (c, events)
    | Restrict (local_events, p) ->
      let count, map, set =
        Iarray.fold_left
          (fun (count, map, set) e ->
             let anon_event = E.anon e count in
             count + 1, EventMap.add e anon_event map, Events.add anon_event set)
          (count, map, set)
          local_events
      in
      refactor_restrict count map set p
    | ComputeValue (lv, f, args, p) ->
      let count, map, set, p = refactor_restrict count map set p in
      count, map, set, ComputeValue (lv, f, args, p)
  ;;

  let refactor_restrict count set p =
    let count, _, set, p = refactor_restrict count EventMap.empty set p in
    count, set, p
  ;;

  let rec as_parallel = function
    | Nil -> []
    | Prefix _ as p -> [ p ]
    | Parallel ps -> List.flat_map as_parallel ps
    | Choice _ as p -> [ p ]
    | Restrict _ | TemplateCall _ | Closure _ | ComputeValue _ ->
      failwith "as_parallel: should be unrolled and refactored out by this point"
  ;;

  type 'a crumbed = int list * 'a

  let rec actions_with_crumbs crumbs : _ -> (E.t, 'a value_expr) action crumbed list
    = function
    | Nil -> []
    | Prefix (a, _) -> [ List.rev crumbs, a ]
    | Parallel ps | Choice ps ->
      List.flatten @@ List.mapi (fun i p -> actions_with_crumbs (i :: crumbs) p) ps
    | Restrict _ | TemplateCall _ | Closure _ | ComputeValue _ ->
      failwith "actions_with_crumbs: should be unrolled and refactored out by this point"
  ;;

  module ProcessID = struct
    open Ppx_compare_lib.Builtin

    type t = int [@@deriving compare]

    let equal id1 id2 = compare id1 id2 = 0
  end

  type 'a record = ProcessID.t * (E.t, 'a value_expr) action crumbed

  type 'a entry =
    { send : 'a record list
    ; receive : 'a record list
    }

  let is_entry_empty { send; receive } = List.is_empty send && List.is_empty receive

  type 'a process_index =
    { ready : Events.t
    ; sync : 'a entry EventMap.t
    ; tau : 'a record list
    }

  let empty_index = { ready = Events.empty; sync = EventMap.empty; tau = [] }

  module Processes = Map.Make (ProcessID)
  module ProcessIDs = Set.Make (ProcessID)

  type 'a t =
    { var_count : int
    ; process_count : int
    ; lib : (T.t, 'a) template Templates.t
    ; hidden_events : Events.t
    ; processes : (T.t, E.t, 'a, 'a) process Processes.t
    ; index : 'a process_index
    }

  let is_ready entry =
    (not (List.is_empty entry.send)) && not (List.is_empty entry.receive)
  ;;

  let push_action ~sending { ready; sync; tau } id crumbs e action =
    let record = id, (crumbs, action) in
    let add_to_entry { send; receive } =
      if sending
      then { send = record :: send; receive }
      else { send; receive = record :: receive }
    in
    let entry = EventMap.value ~default:{ send = []; receive = [] } e sync in
    let entry = add_to_entry entry in
    let ready = if is_ready entry then Events.add e ready else ready in
    let sync = EventMap.add e entry sync in
    { ready; sync; tau }
  ;;

  let index_process idx id p =
    let actions = actions_with_crumbs [] p in
    let index_action idx (crumbs, action) =
      match action with
      | Send (e, _) -> push_action ~sending:true idx id crumbs e action
      | Receive (e, _) -> push_action ~sending:false idx id crumbs e action
      | Tau -> { idx with tau = (id, (crumbs, action)) :: idx.tau }
    in
    List.fold_left index_action idx actions
  ;;

  let index_all_processes processes process_count idx ps =
    List.fold_left
      (fun (process_count, processes, idx) p ->
         let id = process_count in
         let processes = Processes.add id p processes in
         let idx = index_process idx id p in
         process_count + 1, processes, idx)
      (process_count, processes, idx)
      ps
  ;;

  let of_system (templates, process) =
    let lib = Templates.of_seq (List.to_seq templates) in
    let process = unroll ~lib process in
    let var_count, hidden_events, process = refactor_restrict 0 Events.empty process in
    let processes = Processes.empty in
    let process_count = 0 in
    let process_count, processes, index =
      index_all_processes processes process_count empty_index (as_parallel process)
    in
    { var_count; process_count; lib; hidden_events; processes; index }
  ;;

  let remove_process processes { ready = _; sync; tau } id =
    let processes = Processes.remove id processes in
    let filter_record (inline_id, _) = not (ProcessID.equal inline_id id) in
    let rebuild_entry e { send; receive } (ready, sync) =
      let entry =
        { send = List.filter filter_record send
        ; receive = List.filter filter_record receive
        }
      in
      if is_entry_empty entry
      then ready, sync
      else (
        let ready = if is_ready entry then Events.add e ready else ready in
        ready, sync)
    in
    let ready, sync = EventMap.fold rebuild_entry sync (Events.empty, EventMap.empty) in
    let tau = List.filter filter_record tau in
    processes, { ready; sync; tau }
  ;;

  let pick_action { ready; sync; tau } =
    let extract_pair { send; receive } = List.first send, List.first receive in
    match Events.choose_opt ready with
    | Some e -> extract_pair @@ EventMap.find e sync
    | None ->
      (match EventMap.choose_opt sync with
       | Some (_, entry) -> extract_pair entry
       | None -> List.first tau, None)
  ;;

  let rec force_sync crumbs action = function
    | Prefix (a, p) ->
      if List.is_empty crumbs
      then (
        match a, action with
        | Send (e1, _), (Send (e2, _) | Receive (e2, _)) ->
          if E.compare e1 e2 = 0 then p else failwith "sync: wrong event"
        | Receive (e1, var), Send (e2, Defined value) ->
          if E.compare e1 e2 = 0
          then define_var var value p
          else failwith "sync: wrong event"
        | Receive _, Send (_, Ref _) ->
          failwith "sync: value variable was not instantiated"
        | Send _, Tau | Receive _, Tau | Tau, (Send _ | Receive _) ->
          failwith "sync: cannot synchronize with tau"
        | Receive _, Receive _ -> failwith "sync: cannot synchronize "
        | Tau, Tau -> p)
      else failwith "sync: wrong crumb level"
    | Parallel ps ->
      let i, tail = List.uncons crumbs in
      let ps = List.mapi (fun j p -> if i = j then force_sync tail action p else p) ps in
      Parallel ps
    | Choice ps ->
      let i, tail = List.uncons crumbs in
      let p = List.nth ps i in
      force_sync tail action p
    | Nil | Restrict _ | TemplateCall _ | Closure _ | ComputeValue _ ->
      failwith "sync: unreachable"
  ;;

  let execute state action_list =
    let process_action state (id, (crumbs, action)) =
      let p = Processes.find id state.processes in
      let processes, index = remove_process state.processes state.index id in
      let p = force_sync crumbs action p in
      let p = unroll ~lib:state.lib p in
      let var_count, hidden_events, p =
        refactor_restrict state.var_count state.hidden_events p
      in
      let ps = as_parallel p in
      let process_count, processes, index =
        index_all_processes processes state.process_count index ps
      in
      { var_count; hidden_events; process_count; processes; index; lib = state.lib }
    in
    List.fold_left process_action state action_list
  ;;

  type 'v ok =
    | Completed
    | UnmatchedSend of (E.t * 'v t)
    | Sync of E.t option * 'v t

  type error =
    | Receive of E.t
    | HiddenSend of E.t

  type 'v result = ('v ok, error) Result.t

  let reduce_deterministic state =
    match pick_action state.index with
    | Some (p1, (c1, a1)), Some (p2, (c2, a2)) ->
      let e = Option.unwrap ~expect:"" @@ event_opt a1 in
      (* flip the actions for synchronization *)
      Ok (Sync (Some e, execute state [ p1, (c1, a2); p2, (c2, a1) ]))
    | Some (p, ca), None | None, Some (p, ca) ->
      let crumbs, action = ca in
      (match action with
       | Send (e, _) ->
         let state = execute state [ p, (crumbs, action) ] in
         Ok (UnmatchedSend (e, state))
       | Receive (e, _) -> Error (Receive e)
       | Tau ->
         let state = execute state [ p, (crumbs, action) ] in
         Ok (Sync (None, state)))
    | None, None -> Ok Completed
  ;;
end
