open Common
open Prelude
module CCS = CCS

module Make (IDs : Signature.IDs) (Time : Signature.Time) = struct
  open IDs

  module Time = struct
    include Time
    include Interface.ExpOrder.Make (Time)
  end

  module Token = Token.Make (Event) (Time) (Color)
  module EventMap = Map.Make (Event)

  type rw =
    | Read
    | Write
  [@@deriving compare, sexp, show]

  let rw_to_string = function
    | Read -> "r"
    | Write -> "w"
  ;;

  module ActionEvent = struct
    open Ppx_compare_lib.Builtin
    open Ppx_sexp_conv_lib.Conv

    type t =
      | Trace of Event.t * rw
      | Variable of Place.t * rw
      | Queue of Place.t * rw
      | Probe of Probe.t
      | Inject of Color.t
      | Internal of int
      | Anon of t * int
    [@@deriving compare, sexp]

    let anon e i = Anon (e, i)

    let rec to_string = function
      | Trace (e, rw) -> Printf.sprintf "e:%s^%s" (Event.to_string e) (rw_to_string rw)
      | Variable (v, rw) -> Printf.sprintf "v:%s^%s" (Place.to_string v) (rw_to_string rw)
      | Queue (q, rw) -> Printf.sprintf "q:%s^%s" (Place.to_string q) (rw_to_string rw)
      | Probe p -> Printf.sprintf "p:%s" (Probe.to_string p)
      | Inject c -> Printf.sprintf "c:%s" (Color.to_string c)
      | Internal i -> Printf.sprintf "i:%i" i
      | Anon (a, i) -> Printf.sprintf "%s_%i" (to_string a) i
    ;;

    let rv name = Variable (name, Read)
    let wv name = Variable (name, Write)
    let rq name = Queue (name, Read)
    let wq name = Queue (name, Write)
  end

  module Sem = CCS.Semantics (String) (ActionEvent)

  type 'v event_todo =
    { reads : 'v list
    ; writes : 'v list
    }

  let empty_todo = { reads = []; writes = [] }

  (* let of_decl declaration =
    let add_read v map e =
      let entry = EventMap.value ~default:empty_todo e map in
      let entry = { entry with reads = v :: entry.reads } in
      EventMap.add e entry map
    in
    let add_write v map e =
      let entry = EventMap.value ~default:empty_todo e map in
      let entry = { entry with writes = v :: entry.writes } in
      EventMap.add e entry map
    in
    let add_read_writes ~r ~w name reads writes map =
      let map = List.fold_left (add_read (r name)) map reads in
      let map = List.fold_left (add_write (w name)) map writes in
      map
    in
    let event_map = List.fold_left
      Declaration.(
        fun map -> function
          | Variable { name; writes; reads } ->
            add_read_writes ~r:ActionEvent.rv ~w:ActionEvent.wv name reads writes map
          | Queue { name; writes; reads } ->
            add_read_writes ~r:ActionEvent.rq ~w:ActionEvent.wq name reads writes map
          | Inject { at; color } -> add_write (ActionEvent.Inject color) map at
          | Probe { name; at;color=_ } -> add_write (ActionEvent.Probe name) map at)
EventMap.empty
      declaration in 
      let state_actions,state_systems = List.split @@ List.filter_mapi Declaration.( fun i -> function 
      | Variable {name;_} ->
        let w = (ActionEvent.wv name) and r = (ActionEvent.rv name) in  Some ([w;r],CCS.Standard.variable w r (Token.internal))  
      | Queue {name;_} -> let w = (ActionEvent.wq name) and r= (ActionEvent.rq name) in Some ([w;r],CCS.Standard.queue w r (Internal i) )
      | _ -> None) declaration in 
      let state_actions = List.flatten state_actions in
        let define_transition_system e {reads;writes} = 
          let open CCS in 
          let open CCS.Syntax in 
          let ew = ActionEvent.Trace(e, Write) and er = ActionEvent.Trace (e, Read) in 
          let e_in = ArgEvent 0 and e_out = ArgEvent 1 in
          let arg_reads, read_actions = List.split @@ List.mapi (fun i v -> (ArgEvent Number.Integer.( i+2), v)) reads in
          let name = Printf.sprintf "T_e:%s" (Event.to_string e) in 
          let len_reads = List.length read_actions in 
          let arg_writes, write_actions = List.split @@ List.mapi (fun i v -> (ArgEvent Number.Integer.( i+len_reads+2), v)) writes in
          let name = Printf.sprintf "T_e:%s" (Event.to_string e) in 
          
          let token = LocalValue 0 in

          let read_seq = List.fold_lefti (fun p i r -> (r, LocalValue Number.Integer.(i+1)) @? p) write_seq arg_reads in
          let template = (ew, token) @? read_seq in
          [name, template], call name [| ew ; er |] [|  |]
        in 
        EventMap.to_list (EventMap.mapi define_transition_system event_map) in
        
  ;; *)
end
