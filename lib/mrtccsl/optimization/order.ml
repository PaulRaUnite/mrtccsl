open Prelude
open Language

module Make (C : Set.OrderedType) = struct
  module L = Set.Make (C)

  module V = struct
    type t =
      { solutions : int
      ; constr : int
      ; constr_str : string
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

  module Display = struct
    include G

    let vertex_name v = string_of_int (V.hash v)
    let graph_attributes _ = []
    let default_vertex_attributes _ = []
    let vertex_attributes v = [ `Label (V.label v).constr_str ]
    let default_edge_attributes _ = []
    let edge_attributes e = [ `Label (string_of_int (E.label e)) ]
    let get_subgraph _ = None
  end

  module Dot = Graph.Graphviz.Dot (Display)

  let compatible ~modulo l l' = L.equal_modulo ~modulo l l'

  module VS = Set.Make (G.V)

  let root graph component =
    let component = VS.of_list component in
    let iter f = G.iter_edges_e f graph in
    let edge =
      iter
      |> Iter.filter (fun e ->
        let src = G.E.src e in
        VS.mem src component)
      |> Iter.min_exn ~lt:(fun x y -> G.E.label x < G.E.label y)
    in
    [ G.E.src edge; G.E.dst edge ]
  ;;

  let rec optimize graph group_size front clocks =
    if List.length front = group_size
    then front
    else (
      let cardinality = L.cardinal clocks in
      let frontset = VS.of_list front in
      let _, next =
        front
        |> Iter.of_list
        |> Iter.flat_map_l (G.succ_e graph)
        |> Iter.filter_map (fun e ->
          let dst = G.E.dst e in
          let src = G.E.src e in
          let src_label = G.V.label src in
          let dst_label = G.V.label dst in
          if VS.mem dst frontset
          then None
          else
            Some
              ( ( cardinality - L.cardinal (L.inter clocks dst_label.clocks)
                , G.E.label e / src_label.solutions )
              , dst ))
        |> Iter.min_exn ~lt:(fun x y -> fst x < fst y)
      in
      optimize graph group_size (next :: front) (L.union (G.V.label next).clocks clocks))
  ;;

  let squish =
    let open Cstr in
    function
    | Causality { cause; conseq } | Precedence { cause; conseq } ->
      List.powerset [ cause; conseq ]
    | Exclusion { args; _ } -> [] :: List.map List.return args
    | Coincidence clocks -> [ []; clocks ]
    | Subclocking { sub; super; _ } -> [ []; [ sub; super ]; [ super ] ]
    | Minus { out; arg; except } ->
      [ []; [ out; arg ] ]
      @ List.powerset_nz except
      @ List.map (List.cons arg) (List.powerset_nz except)
    | Delay { out; arg; base; _ } ->
      [ []; [ out; base ]; [ out; arg; base ]; [ arg ]; [ arg; base ]; [ base ] ]
    | Fastest { out; args } | Slowest { out; args } ->
      let pws = List.powerset_nz args in
      let with_out = List.map (List.cons out) pws in
      let len = List.length args in
      let without_out = List.filter (fun label -> List.length label <> len) pws in
      ([] :: with_out) @ without_out
    | Intersection { out; args } ->
      let labels = List.powerset args in
      List.map (fun l -> if l = args then out :: args else l) labels
    | Union { out; args } -> [] :: List.map (fun l -> out :: l) (List.powerset_nz args)
    | DisjunctiveUnion { out; args; _ } -> [] :: List.map (fun c -> [ out; c ]) args
    | Periodic { out; base; _ } -> [ []; [ out; base ]; [ base ] ]
    | Sample { out; arg; base } ->
      [ []; [ out; base ]; [ out; base; arg ]; [ arg ]; [ base ] ]
    | Alternate { first; second; strict } ->
      if strict
      then [ []; [ first ]; [ second ] ]
      else [ []; [ first ]; [ second ]; [ first; second ] ]
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
    | Allow { left; right; args; _ } | Forbid { left; right; args; _ } ->
      [ [ left ]; [ right ]; [ left; right ] ] @ List.powerset args
    | Sporadic { out; _ } -> [ [ out ] ]
  ;;

  let squish c = List.map L.of_list @@ squish c

  let edge (labels1, clocks1) (labels2, clocks2) =
    Seq.product (List.to_seq labels1) (List.to_seq labels2)
    |> Seq.filter (fun (x, y) -> compatible ~modulo:(L.inter clocks1 clocks2) x y)
    |> Seq.length
  ;;

  let graph (spec : _ Specification.t) =
    let constr = Array.of_list spec.clock in
    let vertices =
      Array.mapi
        (fun i c ->
           let labels = squish c in
           G.V.create
             { solutions = List.length labels
             ; labels
             ; constr = i
             ; constr_str = Cstr.name c
             ; clocks = L.of_list @@ Cstr.clocks c
             })
        constr
    in
    let iter = Iter.int_range ~start:0 ~stop:(Array.length vertices - 1) in
    let graph =
      Iter.product iter iter
      |> Iter.fold
           (fun m (i, j) ->
              if i >= j
              then m
              else (
                let x = G.V.label vertices.(i)
                and y = G.V.label vertices.(j) in
                if L.is_empty (L.inter x.clocks y.clocks)
                then m
                else (
                  let solutions = edge (x.labels, x.clocks) (y.labels, y.clocks) in
                  if solutions > 0
                  then G.add_edge_e m (G.E.create vertices.(i) solutions vertices.(j));
                  m)))
           (G.create ~size:(Array.length vertices) ())
    in
    constr, graph
  ;;

  let optimize (spec : _ Specification.t) =
    let constr, graph = graph spec in
    let module Components = Graph.Components.Undirected (G) in
    let components = Components.components_list graph in
    let optimize_component component =
      let root = root graph component in
      let clocks =
        List.fold_left L.union L.empty (List.map (fun v -> (G.V.label v).clocks) root)
      in
      optimize graph (List.length component) root clocks
    in
    let constraints =
      List.rev_map
        (fun v -> constr.((G.V.label v).constr))
        (List.flat_map optimize_component components)
    in
    assert (List.length spec.clock = List.length constraints);
    { spec with clock = constraints }
  ;;
end
