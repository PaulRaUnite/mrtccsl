open Prelude
open Language

module Make (C : Set.OrderedType) = struct
  module L = Set.Make (C)

  module V = struct
    type t =
      { solutions : int
      ; constr : int
      ; labels : L.t list
      ; clocks : L.t
      }
  end

  module G =
    Graph.Imperative.Graph.AbstractLabeled
      (V)
      (struct
        include Int

        let default = 0
      end)

  let compatible ~modulo l l' = L.equal_modulo ~modulo l l'

  let seed graph =
    let iter f = G.iter_edges_e f graph in
    let edge = iter |> Iter.min_exn ~lt:(fun x y -> G.E.label x > G.E.label y) in
    [ G.E.src edge; G.E.dst edge ]
  ;;

  module VS = Set.Make (G.V)

  let rec optimize graph front =
    if List.length front = G.nb_vertex graph
    then front
    else (
      let frontset = VS.of_list front in
      let _, next =
        front
        |> Iter.of_list
        |> Iter.flat_map_l (G.succ_e graph)
        |> Iter.filter_map (fun e ->
          let dst = G.E.dst e in
          if VS.mem dst frontset
          then None
          else Some (G.E.label e / (G.V.label dst).solutions, dst))
        |> Iter.min_exn ~lt:(fun x y -> fst x > fst y)
      in
      optimize graph (next :: front))
  ;;

  let squish = function
    | Causality { cause; conseq } | Precedence { cause; conseq } ->
      List.powerset [ cause; conseq ]
    | Exclusion (clocks,_) -> [] :: List.map List.return clocks
    | Coincidence clocks -> [ []; clocks ]
    | Subclocking { sub; super; _ } -> [ []; [ sub; super ]; [ super ] ]
    | Minus { out; arg; except } ->
      [ []; [ out; arg ] ]
      @ List.powerset_nz except
      @ List.map (List.cons arg) (List.powerset_nz except)
    | Delay { out; arg; base; _ } ->
      (match base with
       | Some base ->
         [ []; [ out; base ]; [ out; arg; base ]; [ arg ]; [ arg; base ]; [ base ] ]
       | None -> [ []; [ out; arg ]; [ arg ] ])
    | Fastest { out; args = [ left; right ] } | Slowest { out; args = [ left; right ] } ->
      [ []; [ out; left; right ]; [ out; left ]; [ out; right ]; [ left ]; [ right ] ]
    | Intersection { out; args } ->
      let labels = List.powerset args in
      List.map (fun l -> if l = args then out :: args else l) labels
    | Union { out; args } -> [] :: List.map (fun l -> out :: l) (List.powerset_nz args)
    | Periodic { out; base; _ } -> [ []; [ out; base ]; [ base ] ]
    | Sample { out; arg; base } ->
      [ []; [ out; base ]; [ out; base; arg ]; [ arg ]; [ base ] ]
    | Alternate { first; second } -> [ []; [ first ]; [ second ] ]
    | RTdelay { out; arg; _ } -> List.powerset [ out; arg ]
    | CumulPeriodic { out; _ } | AbsPeriodic { out; _ } -> [ []; [ out ] ]
    | FirstSampled { out; arg; base } | LastSampled { out; arg; base } ->
      [ []; [ out; arg ]; [ arg ]; [ out; arg; base ]; [ base ]; [ arg; base ] ]
    | Pool (n, pairs) ->
      pairs
      |> List.map (fun (x, y) -> [ []; [ x ]; [ y ] ])
      |> List.powerset_nz
      |> List.filter (fun l -> List.length l <= n)
      |> List.flat_map (fun comb -> List.fold_left List.flat_cartesian [ [] ] comb)
    | _ -> failwith "not implemented"
  ;;

  let squish c = List.map L.of_list @@ squish c

  let edge (labels1, clocks1) (labels2, clocks2) =
    Seq.product (List.to_seq labels1) (List.to_seq labels2)
    |> Seq.filter (fun (x, y) -> compatible ~modulo:(L.inter clocks1 clocks2) x y)
    |> Seq.length
  ;;

  let optimize (spec : _ Specification.t) =
    let constr = Array.of_list spec.logical in
    let vertices =
      Array.mapi
        (fun i c ->
           let labels = squish c in
           G.V.create
             { solutions = List.length labels
             ; labels
             ; constr = i
             ; clocks = L.of_list @@ clocks c
             })
        constr
    in
    let iter = Iter.int_range ~start:0 ~stop:(Array.length vertices - 1) in
    let graph =
      Iter.product iter iter
      |> Iter.fold
           (fun m (i, j) ->
              let x = G.V.label vertices.(i)
              and y = G.V.label vertices.(j) in
              let solutions = edge (x.labels, x.clocks) (y.labels, y.clocks) in
              if solutions > 0
              then G.add_edge_e m (G.E.create vertices.(i) solutions vertices.(j));
              m)
           (G.create ~size:(Array.length vertices) ())
    in
    let constraints =
      List.map (fun v -> constr.((G.V.label v).constr)) (optimize graph (seed graph))
    in
    { spec with logical = constraints }
  ;;
end
