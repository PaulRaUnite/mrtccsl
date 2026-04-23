module type Platform = sig
  type signal_id

  type pattern =
    | Variable
    | Queue

  module Ingress : sig
    type 'a t

    val read : 'a t -> 'a
    val write : 'a t -> 'a -> unit
  end

  module Egress : sig
    type 'a t

    val read : 'a t -> 'a
    val write : 'a t -> 'a -> unit
  end

  type t

  val create : unit -> t
  val ingress : signal_id -> pattern -> t -> 'a Ingress.t * t
  val egress : signal_id -> t -> 'a Egress.t * t

  module Task : sig
    type t

    val periodic : period:int -> exec:(unit -> unit) -> t
    val event_triggered : event:signal_id -> exec:(unit -> unit) -> t
  end

  val run_parallel : Task.t -> t -> unit
end

type 's triggering =
  | OnEvent of 's
  | PeriodicMS of int

type ('m, 's) component =
  { trigger : 's triggering
  ; exec_capture : 'm -> unit -> unit
  }

type ('m, 's) system_def = { components : ('m, 's) component list }

module Definition (P : Platform) = struct
  open P

  let of_system { components } =
    let mesh = P.create () in
    let components =
      List.map
        (fun { trigger; exec_capture } ->
           let exec = exec_capture mesh in
           let task =
             match trigger with
             | OnEvent event -> Task.event_triggered ~event ~exec
             | PeriodicMS period -> Task.periodic ~period ~exec
           in
           task)
        components
    in
    components
  ;;
end
