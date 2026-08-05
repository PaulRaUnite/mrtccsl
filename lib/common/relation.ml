open Prelude

module Transitive = struct
  (** Relation is indicated by tags. Each set element can relate to several tags (for example, variables). [T] is for tags. *)
  module ByTag (T : Interface.TotalOrder) = struct
    module TagMap = Map.Make (T)

    let empty = TagMap.empty

    let add ~tag tag_to_component e =
      let tag_set = tag e in
      let existing_components =
        List.filter_map (fun tag -> TagMap.find_opt tag tag_to_component) tag_set
      in
      let new_component = UnionFind.make [ e ] in
      let do_union = UnionFind.merge List.append in
      let union_component = List.fold_left do_union new_component existing_components in
      let tag_to_component =
        List.fold_left
          (fun m tag -> TagMap.add tag union_component m)
          tag_to_component
          tag_set
      in
      tag_to_component
    ;;

    let components tag_to_component =
      let components =
        tag_to_component
        |> TagMap.to_seq
        |> Seq.filter_map (fun (_, v) ->
          if UnionFind.is_representative v then Some (UnionFind.get v, ()) else None)
        |> Hashtbl.of_seq
      in
      Hashtbl.to_seq_keys components
    ;;
  end
end
