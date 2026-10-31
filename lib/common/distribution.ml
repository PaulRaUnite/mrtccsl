open Prelude

module Discrete = struct
  type 'a t = { ratios : ('a * int) list }

  let truncate { ratios } interval =
    let left, right = Interval.Int.to_nonstrict interval in
    let available =
      List.filter (fun (value, _) -> left <= value && value <= right) ratios
    in
    { ratios = available }
  ;;

  type 'a compiled =
    { ratios : ('a * int) list
    ; sum : int
    }

  let compile ({ ratios } : _ t) =
    let sum = List.fold_left (fun acc (_, ratio) -> acc + ratio) 0 ratios in
    { ratios; sum }
  ;;

  let rvs { ratios; sum } () =
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
        ratios
    in
    Option.get chosen
  ;;

  let to_rvs ratios interval = rvs @@ compile @@ truncate { ratios } interval
end

module Continuous = struct
  type kernel =
    | NormalKernel
    | ParabolicKernel
    | TriangularKernel
    | BiweightKernel
    | TriweightKernel
    | UniformKernel
  [@@deriving show]

  (** Variants of continuous-valued distributions that can be used in a simulation. *)
  type 'n t =
    | Uniform
    | Normal of
        { mean : 'n
        ; deviation : 'n
        }
    | Exponential of { rate : 'n }
    | Histogram of { resolution : 'n }
    | Kernel of
        { bandwidth : 'n
        ; kernel : kernel
        }
      (* kernel density estimation *)
  [@@deriving map, show, fold]

  module type S = sig
    type num
    type bound

    val to_rvs : num t -> bound -> unit -> num
  end

  module Make
      (N : sig
         type t

         val equal : t -> t -> bool
         val to_string : t -> string
         val to_float : t -> float
         val of_float : float -> t
         val random : t -> t -> t
       end)
      (NI : Interval.I with type num = N.t) =
  struct

    type num = N.t
    type bound = NI.t

    let rec repeat_if_equal rand value =
      let rvs = rand () in
      if N.equal rvs value then repeat_if_equal rand value else rvs
    ;;

    let rec repeat_if_equal2 rand v1 v2 =
      let rvs = rand () in
      if N.equal rvs v1
      then repeat_if_equal2 rand v1 v2
      else if N.equal rvs v2
      then repeat_if_equal2 rand v1 v2
      else (
        print_endline (N.to_string rvs);
        rvs)
    ;;

    let to_rvs ~load_histogram_rvs name def bounds =
      let open Number in
      match def with
      | Uniform ->
        NI.(
          (match bounds with
           | Bound (Include lower, Include upper) -> fun () -> N.random lower upper
           | Bound (Include lower, Exclude upper) ->
             fun () -> repeat_if_equal (fun () -> N.random lower upper) upper
           | Bound (Exclude lower, Include upper) ->
             fun () -> repeat_if_equal (fun () -> N.random lower upper) lower
           | Bound (Exclude lower, Exclude upper) ->
             fun () -> repeat_if_equal2 (fun () -> N.random lower upper) lower upper
           | _ -> failwith "uniform distribution is undefined on infinite intervals"))
      | Normal { mean; deviation } ->
        let mu = N.to_float mean in
        let sigma = N.to_float deviation in
        let bounds =
          Option.unwrap ~expect:"gaussian distribution is undefined on exclusive bounds"
          @@ NI.constant_bounds bounds
        in
        let a, b = Tuple.map2 N.to_float bounds in
        fun () ->
          let sample = Float.truncated_guassian_rvs ~a ~b ~mu ~sigma in
          N.of_float sample
      | Exponential { rate } ->
        let rate = N.to_float rate in
        (match NI.constant_bounds bounds with
         | None -> fun () -> N.of_float @@ Float.exponential_rvs ~rate
         | Some bounds ->
           let a, b = Tuple.map2 N.to_float bounds in
           fun () ->
             let sample = Float.truncated_exponential_rvs ~a ~b ~rate in
             N.of_float sample)
      | Histogram { resolution } -> load_histogram_rvs name resolution
      | _ -> failwith "Kernel density estimation is not implemented"
    ;;
  end
end

(** Identically and independently distributed (IID) sequence of values. *)
module IIDSeq = struct
  type 'n sampler = unit -> 'n

  type 'n t =
    { mutable value : 'n
    ; sampler : 'n sampler
    }

  let make sampler = { value = sampler (); sampler }
  let of_const value = { value; sampler = (fun () -> value) }
  let get_sample { value; _ } = value
  let update_sample seq = seq.value <- seq.sampler ()
end

(** Map of Identically and independently distributed (IID) sequences associated to variables.*)
module IIDSeqMap (VMap : Map.S) = struct
  type 'v t =
    { default : 'v
    ; vars : 'v IIDSeq.t VMap.t
    }

  let make ~default vars = { default; vars }
  let empty ~default = make ~default VMap.empty

  let get_value { vars; default } var =
    let seq = VMap.find_opt var vars in
    Option.map_or ~default IIDSeq.get_sample seq
  ;;

  let get { vars; _ } var =
    let seq = VMap.find var vars in
    IIDSeq.(seq.value)
  ;;

  let update { vars; _ } var = IIDSeq.update_sample (VMap.find var vars)

  let get_handle { default; vars } var =
    match VMap.find_opt var vars with
    | Some seq -> (fun () -> IIDSeq.get_sample seq), fun () -> IIDSeq.update_sample seq
    | None ->
      print_endline "default handle";
      (fun () -> default), fun () -> ()
  ;;

  let to_string ks vs { vars; _ } = VMap.to_string ks (fun v -> vs IIDSeq.(v.value)) vars
end
