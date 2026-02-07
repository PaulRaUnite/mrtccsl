open Prelude

module AsDefined = struct
  module V = struct
    type t =
      | Clock of string
      | Constraint of string
  end

  module E = struct
    type t = unit

    let compare () () = 0
    let default = ()
    let to_string () = ""
  end

  module G = Graph.Imperative.Digraph.AbstractLabeled (V) (E)

  module Dot = Graph.Graphviz.Dot (struct
      include G

      let vertex_name v = string_of_int (V.hash v)
      let graph_attributes _ = []
      let default_vertex_attributes _ = []

      let vertex_attributes v =
        match V.label v with
        | Clock s -> [ `Label s ]
        | Constraint s -> [ `Label s; `Shape `Box ]
      ;;

      let default_edge_attributes _ = []
      let edge_attributes _ = []
      let get_subgraph _ = None
    end)

  type 'c definition = string * ('c list * 'c list)

  let of_constraint c : _ definition option =
    let open Language.Cstr in
    let def =
      match c with
      | Minus { out; arg; except } -> Some (arg :: except, out)
      | Delay { out; arg; base; _ } -> Some ([ arg; base ], out)
      | Fastest { out; args } | Slowest { out; args } -> Some (args, out)
      | Intersection { out; args }
      | Union { out; args }
      | DisjunctiveUnion { out; args; _ } -> Some (args, out)
      | Periodic { out; base; _ } -> Some ([ base ], out)
      | Sample { out; arg; base }
      | FirstSampled { out; arg; base }
      | LastSampled { out; arg; base } -> Some ([ arg; base ], out)
      | RTdelay { out; arg; _ } -> Some ([ arg ], out)
      | CumulPeriodic { out; _ } | AbsPeriodic { out; _ } -> Some ([], out)
      | Coincidence [ left; right ] -> Some ([ right ], left)
      | _ -> None
    in
    let name = name c in
    match def with
    | Some (inputs, output) -> Some (name, (inputs, [ output ]))
    | None ->
      let cs = clocks c in
      Some (name, (cs, cs))
  ;;

  let of_spec clock_to_string spec =
    let clocks_to_vertices = Hashtbl.create 32 in
    let graph = G.create () in
    let map_clock c =
      match Hashtbl.find_opt clocks_to_vertices c with
      | Some v -> v
      | None ->
        let v = G.V.create (Clock (clock_to_string c)) in
        G.add_vertex graph v;
        Hashtbl.add clocks_to_vertices c v;
        v
    in
    let process_constraint constr =
      Option.value
        ~default:()
        (let* name, (inputs, outputs) =
           of_constraint
             (Language.Cstr.map_clock_constr map_clock Fun.id Fun.id Fun.id Fun.id Fun.id constr)
         in
         let constraint_vertex = G.V.create (Constraint name) in
         List.iter
           (fun input_clock ->
              G.add_edge_e graph (G.E.create input_clock () constraint_vertex))
           inputs;
         List.iter
           (fun output_clock ->
              G.add_edge_e graph (G.E.create constraint_vertex () output_clock))
           outputs;
         Some ())
    in
    List.iter process_constraint Language.Specification.(spec.clock);
    graph
  ;;
end
