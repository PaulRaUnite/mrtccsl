open Common

module Make (N : Trace.Timestamp) (L : Trace.Label) = struct
  module Serialize = struct
    (** [undefined] serializes the step in order defined by the label implementation.*)
    let undefined l = L.to_iter l

    (** [random] serializes the step in randomly.*)
    let random l = l |> L.to_iter |> Iter.shuffle

    (** [respect_microstep] serializes the step randomly while respecting partial ordering.*)
    let respect_microstep order_hints l =
      l
      |> L.to_iter
      |> Microstep.HardRelation.arrange_randomly order_hints
      |> Iter.of_list
    ;;
  end

  module Tag = struct
    let none = (fun () -> ()), fun () _ l -> l

    let tag_round_timestamp round =
      let init () = ref N.zero
      and tag previous_aligned now serialization =
        let n_steps, diff_aligned, _ = round N.(now - !previous_aligned) in
        (previous_aligned := N.(!previous_aligned + diff_aligned));
        serialization
        |> Iter.zip_i
        |> Iter.map (fun (i, e) ->
          Printf.sprintf "%s %i" e (if i = 0 then n_steps else 0))
      in
      init, tag
    ;;
  end
end
