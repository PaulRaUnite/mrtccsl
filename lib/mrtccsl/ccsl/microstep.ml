open Prelude

module HardRelation = struct
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

  type 'a compiled = ('a, ('a, 'a) Either.t list) Hashtbl.t

  let compile relations : _ compiled =
    List.fold_left
      (fun tbl (cause, conseq) ->
         Hashtbl.entry (List.cons (Either.Left conseq)) ~default:[] cause tbl;
         Hashtbl.entry (List.cons (Either.Right cause)) ~default:[] conseq tbl;
         tbl)
      (Hashtbl.create 16)
      relations
  ;;

  (** Orders present causaly-related clocks inside the [label] as indicated in [restrictions], thus the information about causality should be supplied per step basis.*)
  let arrange_randomly (comp_rel : _ compiled) label =
    let module I = Interval.Make (Number.Integer) in
    let label, _ =
      Iter.foldi
        (fun (ordered_label, index) len event ->
           let placement_hints =
             Option.value ~default:[] (Hashtbl.find_opt comp_rel event)
           in
           let allowed_interval =
             List.fold_left
               (fun interval hint ->
                  let placement =
                    match hint with
                    | Either.Left event ->
                      let* i = Hashtbl.find_opt index event in
                      Some (I.ninf i)
                    | Either.Right event ->
                      let* i = Hashtbl.find_opt index event in
                      Some (I.pinf (i + 1))
                  in
                  Option.map_or ~default:interval (I.inter interval) placement)
               (I.make_include 0 len)
               placement_hints
           in
           let min, max =
             I.constant_bounds allowed_interval
             |> Option.unwrap ~expect:"causality relations need to be compatible"
           in
           let insert_index = Random.int_in_range ~min ~max in
           let ordered_label = List.insert ordered_label event insert_index
           and index =
             Hashtbl.map_v (fun i -> if i >= insert_index then i + 1 else i) index
           in
           Hashtbl.add index event insert_index;
           ordered_label, index)
        ([], Hashtbl.create 16)
        label
    in
    label
  ;;
end
