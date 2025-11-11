open Prelude

(*WARNING: to be deprecated as the ordering should be supplied by the constraints themselves, per label/step basis.*)
let derive_order spec =
  spec
  |> List.filter_map
       Language.(
         function
         | Causality { cause; conseq } -> Some (cause, conseq)
         | RTdelay { arg; out; _ } -> Some (arg, out)
         | _ -> None)
  |> List.concat_map (fun (cause, conseq) ->
    [ conseq, Either.Right cause; cause, Either.Left conseq ])
  |> List.fold_left
       (fun tbl (event, restriction) ->
          Hashtbl.entry (List.cons restriction) ~default:[] event tbl;
          tbl)
       (Hashtbl.create 16)
;;

(*WARNING: this implementation orders any present causaly-related clocks inside the step, thus the information about causality should be supplied per step basis.*)
let arrange_randomly restrictions label =
  let module I = Interval.Make (Number.Integer) in
  let label, _ =
    Iter.foldi
      (fun (ordered_label, index) len event ->
         let placement_hints =
           Option.value ~default:[] (Hashtbl.find_opt restrictions event)
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
