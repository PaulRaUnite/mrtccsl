open Common
open Prelude

module type K = sig
  include Map.OrderedType

  val to_string : t -> string
  val hash : t -> int
  val equal : t -> t -> bool
end

module HardRelation (K : K) = struct
  (** Type denoting relation [x before y]. *)
  type 'id t = 'id * 'id [@@deriving sexp]

  let of_logical_spec spec : _ t list =
    List.filter_map
      Language.Cstr.(
        function
        | Causality { cause; conseq } -> Some (cause, conseq)
        | RTdelay { arg; out; _ } -> Some (arg, out)
        | _ -> None)
      spec
  ;;

  let spec_of_sexp id_of_sexp sexp =
    Sexplib0.Sexp_conv.list_of_sexp (t_of_sexp id_of_sexp) sexp
  ;;

  let sexp_of_spec sexp_of_id sexp =
    Sexplib0.Sexp_conv.sexp_of_list (sexp_of_t sexp_of_id) sexp
  ;;

  module G = Graph.Persistent.Digraph.Concrete (K)
  module O = Graph.Oper.P (G)

  type compiled = G.t

  let compile relations : compiled =
    let g = G.empty in
    let g = List.fold_left (fun g (cause, conseq) -> G.add_edge g cause conseq) g relations in 
    O.transitive_closure g
  ;;

  (** Orders present causaly-related clocks inside the [label] as indicated in [restrictions], thus the information about causality should be supplied per step basis.*)
  let arrange_randomly (comp_rel : compiled) label =
    let module M = Map.Make (K) in
    let module I = Interval.Int in
    let label, _ =
      Iter.foldi
        (fun (ordered_label, index) len event ->
           let basic_interval = I.make_include 0 len in
           let allowed_interval =
             G.fold_succ
               (fun conseq interval ->
                  let placement =
                    let* i = M.find_opt conseq index in
                    Some (I.ninf i)
                  in
                  Option.map_or ~default:interval (I.inter interval) placement)
               comp_rel
               event
               basic_interval
           in
           let allowed_interval =
             G.fold_pred
               (fun cause interval ->
                  let placement =
                    let* i = M.find_opt cause index in
                    Some (I.pinf (i + 1))
                  in
                  Option.map_or ~default:interval (I.inter interval) placement)
               comp_rel
               event
               allowed_interval
           in
           let min, max =
             I.constant_bounds allowed_interval
             |> Option.unwrap ~expect:"causality relations need to be compatible"
           in
           let insert_index = Random.int_in_range ~min ~max in
           let ordered_label = List.insert ordered_label event insert_index
           and index = M.map (fun i -> if i >= insert_index then i + 1 else i) index in
           ordered_label, M.add event insert_index index)
        ([], M.empty)
        label
    in
    label
  ;;
end
