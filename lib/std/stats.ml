open Prelude

module Make
    (Category : sig
       include Map.OrderedType
       include Interface.Stringable with type t := t
     end)
    (Num : sig
       include Interface.Number.Field
       include Map.OrderedType with type t := t
       include Interface.Stringable with type t := t

       val from_pair : int * int -> t
     end) =
struct
  module Categories = Map.Make (Category)
  module CategorySet = Set.Make (Category)
  module Bins = Map.Make (Num)

  type t =
    { bins : Num.t Categories.t Bins.t
    ; categories : CategorySet.t
    ; total : int
    }

  let histogram round_to (reaction_times : ('key * Num.t) Iter.t) : t =
    let inc_category k categories = Categories.entry Int.succ ~default:0 k categories in
    let categories, bins, total =
      Iter.fold
        (fun (categories, bins, sum) (k, v) ->
           let bin = round_to v in
           let categories = CategorySet.add k categories
           and bins = Bins.entry ~default:Categories.empty (inc_category k) bin bins in
           categories, bins, sum + 1)
        (CategorySet.empty, Bins.empty, 0)
        reaction_times
    in
    let normalized_bins =
      Bins.map (Categories.map (fun count -> Num.from_pair (count, total))) bins
    in
    { bins = normalized_bins; categories; total }
  ;;

  let to_csv fmt { bins; categories; _ } =
    (* Printf.printf "number of bins: %i\n" (Bins.cardinal bins) ; *)
    let pp_category = fun fmt c -> Format.fprintf fmt "%s" (Category.to_string c) in
    let pp_num fmt n = Format.fprintf fmt "%s" (Num.to_string n) in
    let pp_sep fmt () = Format.pp_print_string fmt "," in
    Format.fprintf
      fmt
      "bin,total,%a\n"
      (Format.pp_print_list ~pp_sep pp_category)
      (CategorySet.to_list categories);
    let categories =
      categories
      |> CategorySet.to_seq
      |> Seq.map (fun k -> k, Num.zero)
      |> Categories.of_seq
    in
    Bins.iter
      (fun bin cats ->
         let cats = Categories.union (fun _k v1 _v2 -> Some v1) cats categories in
         let sum = Categories.fold (fun _ v sum -> Num.add v sum) cats Num.zero in
         let pp_map fmt map =
           Format.pp_print_seq ~pp_sep pp_num fmt (Seq.map snd (Categories.to_seq map))
         in
         Format.fprintf fmt "%a,%a,%a\n" pp_num bin pp_num sum pp_map cats)
      bins;
    Format.pp_print_flush fmt ()
  ;;
end
