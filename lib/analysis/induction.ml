open Prelude

module type Var = sig
  open Interface
  include OrderedType
  include Debug with type t := t
end

module type Num = sig
  open Interface
  include OrderedType
  include Number.Field with type t := t
  include Debug with type t := t
end

module Solver = struct
  open Denotational

  module type S = sig
    type t
    type v
    type n
    type f = (v, n) bool_expr

    val of_formula : f -> t
    val sat : t -> bool
    val ( <= ) : t -> t -> bool
    val ( && ) : t -> t -> t
    val diff : t -> t -> t list
    val more_precise : t -> t -> bool
    val index_name : v
    val infinite_in : v -> t -> bool
    val sat : t -> bool
    val ( && ) : t -> t -> t
    val ( <= ) : t -> t -> bool
    val set_debug : bool -> unit
    val project : v list -> t -> t

    include Interface.Stringable with type t := t
  end

  module type D = sig
    include Domain.S

    val index_name : v
  end

  module MakeFromDomain
      (V : Var)
      (N : Domain.Num)
      (D : D with type v = V.t and type n = N.t) =
  struct
    include D

    type f = (v, n) bool_expr

    let of_formula f =
      add_constraint
        D.index_name
        (D.top D.index_name (BoolExpr.unique_vars V.compare f))
        f
    ;;

    let sat = not << is_bottom
    let ( && ) = meet
    let ( <= ) = leq
  end
end

module Make (C : Var) (N : Num) (S : Solver.S with type v = C.t and type n = N.t) = struct
  open Rtccsl
  open Denotational
  include MakeDebug (C) (N)

  module N = struct
    include N
    include Interface.ExpOrder.Make (N)
  end

  include MakeExpr (C) (N)

  exception ExactRelationUnavailable of (C.t, C.t, N.t) Rtccsl.constr
  exception OverApproximationUnavailable of (C.t, C.t, N.t) Rtccsl.constr
  exception UnderApproximationUnavailable of (C.t, C.t, N.t) Rtccsl.constr

  (** Returns exact semi-linear denotational relation of a RTCCSL constraint. Raises [ExactRelationUnavailable] otherwise.*)
  let exact_rel c =
    let open Syntax in
    let i = 0 in
    (*dummy variable*)
    match c with
    | Precedence { cause; effect } -> cause.@[i] < effect.@[i]
    | Causality { cause; effect } -> cause.@[i] <= effect.@[i]
    | Coincidence list ->
      let maybe_pair_chain =
        List.fold_left
          (fun acc c ->
            match acc with
            | None -> Some (c, [])
            | Some (p, tail) -> Some (c, (p.@[i] == c.@[i]) :: tail))
          None
          list
      in
      let pair_chain =
        (Option.fold ~none:[] ~some:(fun (_, list) -> list)) maybe_pair_chain
      in
      And pair_chain
    | Alternate { first; second } -> first.@[i] &|> (second.@[i - 1], second.@[i])
    | RTdelay { out; arg; delay = e1, e2 } ->
      let e1 = time_param e1 in
      let e2 = time_param e2 in
      out.@[i] &- arg.@[i] &|> (e1, e2)
      && e1 >= Const N.zero
      && e2 >= Const N.zero
      && e2 >= e1
    | Delay { out; arg; delay = IntConst d1, IntConst d2; base = None } when d1 = d2 ->
      out.@[i - d1] == arg.@[i]
    | Fastest { out; left; right } -> out.@[i] == min left.@[i] right.@[i]
    | Slowest { out; left; right } -> out.@[i] == max left.@[i] right.@[i]
    | CumulPeriodic { out; period; error = le, re; offset } ->
      let period, le, re, offset = Tuple.map4 time_param (period, le, re, offset) in
      let prev = ZeroCond (out.@[i - 1], offset &- period) in
      out.@[i] &- prev &- period &|> (le, re)
      && period > Const N.zero
      && re >= le
      && offset > Const N.zero
    | AbsPeriodic { out; period; error = le, re; offset } ->
      let period, le, re, offset = Tuple.map4 time_param (period, le, re, offset) in
      out.@[i] &- (period &* Var (Index (i - 1))) &- offset &|> (le, re)
      && period > Const N.zero
      && re >= le
      && offset > Const N.zero
    | Sporadic { out; at_least; strict } ->
      let diff = out.@[i] &- out.@[i - 1] in
      let at_least = time_param at_least in
      if strict then diff > at_least else diff >= at_least
    | TimeParameter (v, (e1, e2)) ->
      Var (FreeVar v) &|> (num_expr_of_expr e1, num_expr_of_expr e2)
    | _ -> raise (ExactRelationUnavailable c)
  ;;

  let exact_spec (s : ('c, 'p, 'n) specification) : ('c, 'n) bool_expr list =
    List.map exact_rel s
  ;;

  (** Returns overapproximation denotational relation of a RTCCSL constraint. Raises [OverApproximationUnavailable] otherwise.*)
  let over_rel c =
    let open Syntax in
    let i = 0 in
    match c with
    | Exclusion list ->
      let pairwise_exclusions =
        Seq.product (List.to_seq list) (List.to_seq list)
        |> Seq.filter (fun (c1, c2) -> C.compare c1 c2 <> 0)
        |> Seq.map (fun (c1, c2) -> c1.@[i] != c2.@[i])
        |> List.of_seq
      in
      And pairwise_exclusions
    | _ -> raise (OverApproximationUnavailable c)
  ;;

  (** [safe_ver_rel c] returns overapproximation defined in [over_rel] or empty rel (always valid overapproximation).*)
  let over_rel_priority_exact c =
    try over_rel c with
    | OverApproximationUnavailable _ ->
      let clocks = Rtccsl.clocks c in
      And (List.map (fun c -> Syntax.(c.@[-1] < c.@[0])) clocks)
  ;;

  let over_rel_priority_exact_spec = List.map (BoolExpr.norm << over_rel_priority_exact)

  let over_rel_priority_over c =
    try over_rel c with
    | OverApproximationUnavailable _ -> exact_rel c
  ;;

  (** [under_rel c] returns underapproximation denotational relation of [c] constraint. Raises [UnderApproximationUnavailable] if doesn't exist.*)
  let rec under_rel c =
    let open Syntax in
    let i = 0 in
    match c with
    | Exclusion list ->
      let maybe_pair_chain =
        List.fold_left
          (fun acc c ->
            match acc with
            | None -> Some (c, c, [])
            | Some (first, prev, conds) -> Some (first, c, (prev.@[i] < c.@[i]) :: conds))
            (*order the clocks*)
          None
          list
      in
      let pair_chain =
        (Option.fold ~none:[] ~some:(fun (first, last, conds) ->
           (last.@[i - 1] < first.@[i]) :: conds))
          (*close the chain with last clock in the past*)
          maybe_pair_chain
      in
      And pair_chain
    | Subclocking { sub; super } -> sub.@[i] == super.@[i]
    | Minus { out; arg; except } ->
      let exclude_arg_except = under_rel (Exclusion (List.append except [ arg ])) in
      (out.@[i] == arg.@[i] || out.@[i - 1] == arg.@[i - 1]) && exclude_arg_except
    | Intersection { out; args } | Union { out; args } ->
      exact_rel (Coincidence (out :: args))
    | Sample { out; arg; base } ->
      base.@[i] == out.@[i] && base.@[i - 1] < arg.@[i] && arg.@[i] <= base.@[i]
    | Delay { out; arg; delay = IntConst d1, IntConst d2; base = Some base } when d1 = d2
      ->
      out.@[i - d1] == base.@[i]
      && base.@[i - 1 - d1] < arg.@[i - d1]
      && arg.@[i - d1] <= base.@[i - d1]
    | AbsPeriodic { out; period; error; offset }
    | CumulPeriodic { out; period; error; offset } ->
      exact_rel (AbsPeriodic { out; period; error; offset })
    | FirstSampled { out; arg; base } | LastSampled { out; arg; base } ->
      base.@[i - 1] < out.@[i] && out.@[i] == arg.@[i] && arg.@[i] <= base.@[i]
    | Forbid { from; until; args } ->
      And
        (List.map
           (fun a ->
             (from.@[i] <= until.@[i] && until.@[i - 1] < a.@[i] && a.@[i] < from.@[i])
             || (from.@[i - 1] <= until.@[i - 1]
                 && until.@[i - 1] < a.@[i]
                 && a.@[i] < from.@[i]))
           args)
    | Allow { from; until; args } ->
      And (List.map (fun a -> from.@[i] <= a.@[i] && a.@[i] <= until.@[i]) args)
    | _ -> raise (UnderApproximationUnavailable c)
  ;;

  let under_rel_priority_exact c =
    try exact_rel c with
    | ExactRelationUnavailable _ -> under_rel c
  ;;

  let under_rel_priority_under c =
    try under_rel c with
    | UnderApproximationUnavailable _ -> exact_rel c
  ;;

  let safe_exact_rel_spec spec =
    try Some (List.map (BoolExpr.norm << exact_rel) spec) with
    | ExactRelationUnavailable _ -> None
  ;;

  let safe_under_rel_priority_exact_spec spec =
    try Some (List.map (BoolExpr.norm << under_rel_priority_exact) spec) with
    | ExactRelationUnavailable _ | OverApproximationUnavailable _ -> None
  ;;

  let lc_connection c i = Denotational.Syntax.(c.@[i - 1] < c.@[i])

  module SetCI = Set.Make (struct
      type t = C.t * int

      let compare (c1, i1) (c2, i2) =
        let comp = C.compare c1 c2 in
        if comp = 0 then Int.compare i1 i2 else comp
      ;;
    end)

  let rec connect_indices c = function
    | [] | _ :: [] -> []
    | x :: y :: tail ->
      Denotational.Syntax.(c.@[x] < c.@[y]) :: connect_indices c (y :: tail)
  ;;

  let connect_clocks (c, indices) =
    let min, max = List.minmax Int.compare indices in
    let indices = Seq.int_seq_inclusive (min, max) |> List.of_seq in
    List.to_seq (connect_indices c indices)
  ;;

  module SetOCI = Set.Make (struct
      type t = C.t option * int

      let compare (c1, i1) (c2, i2) =
        let comp = Option.compare C.compare c1 c2 in
        if comp = 0 then Int.compare i1 i2 else comp
      ;;
    end)

  let logical_clocks_from_vars present_vars =
    SetCI.fold
      (fun (c, i) tbl ->
        Hashtbl.entry tbl (fun list -> i :: list) c [];
        tbl)
      present_vars
      (Hashtbl.create 32)
  ;;

  module MapOC = Map.Make (struct
      type t = C.t option

      let compare = Option.compare C.compare
    end)

  let clock_index_ranges formula =
    let rule v acc =
      match v with
      | FreeVar _ -> acc
      | Index i -> MapOC.entry (fun (l, r) -> Int.(min i l, max i r)) (i, i) acc None
      | ClockVar (c, i) ->
        MapOC.entry (fun (l, r) -> Int.(min i l, max i r)) (i, i) acc (Some c)
    in
    BoolExpr.fold_vars rule MapOC.empty formula
  ;;

  let ranges_union r =
    let reduce _ (lmin, lmax) = function
      | Some (gmin, gmax) -> Some (Int.min lmin gmin, Int.max lmax gmax)
      | None -> Some (lmin, lmax)
    in
    MapOC.fold reduce r None
  ;;

  (** Construsts inductive precondition from postcondition [post].*)
  let precondition post = BoolExpr.map_idx (fun _ i -> i - 1) post

  (**Intersects all [formulae] with logical clocks related to their past.*)
  let inductive_step product =
    let ranges = clock_index_ranges product in
    let connections_to_past =
      ranges
      |> MapOC.to_seq
      |> Seq.filter_map (fun (v, (min, _)) ->
        let* v = v in
        Some (lc_connection v min))
      |> List.of_seq
    in
    And (product :: connections_to_past)
  ;;

  module MapOCI = Map.Make (struct
      type t = C.t option * int

      let compare = Tuple.compare2 (Option.compare C.compare) Int.compare
    end)

  module OptVarSet = Set.Make (struct
      type t = C.t option

      let compare = Option.compare C.compare
    end)

  let components_by_vars formulae =
    let formulae_with_vars =
      List.map
        (fun f -> [ f ], OptVarSet.of_list (BoolExpr.indexed_vars_except_index f))
        formulae
    in
    let rec add_to_components components (fs, vars) =
      match components with
      | [] -> [ fs, vars ]
      | (fs', vars') :: tail ->
        if OptVarSet.disjoint vars vars'
        then (fs', vars') :: add_to_components tail (fs, vars)
        else add_to_components tail (fs @ fs', OptVarSet.union vars vars')
    in
    let components = List.fold_left add_to_components [] formulae_with_vars in
    List.map (fun (l, _) -> l) components
  ;;

  module VarFormulaGraph = Graph.Imperative.Digraph.Concrete (struct
      type t = int * C.t option * int

      let compare = Tuple.compare3 Int.compare (Option.compare C.compare) Int.compare
      let equal x y = compare x y = 0
      let hash = Hashtbl.hash
    end)

  module ProductGraph = Graph.Traverse.Dfs (VarFormulaGraph)

  type cover =
    | Initial of (int * int)
    | Update of
        { left : (int * int) option
        ; right : (int * int) option
        }

  module ExprSet = Set.Make (struct
      type t = (C.t, N.t) bool_expr

      let compare = BoolExpr.compare
    end)

  exception ProductLoop

  let range_saturate formulae =
    match List.length formulae with
    | 0 -> invalid_arg "range_saturate: cannot saturate zero formulae"
    | 1 -> formulae
    | _ ->
      let spawned_variables = ref MapOC.empty in
      let g = VarFormulaGraph.create () in
      let update_graph v destination =
        match MapOC.find_opt v !spawned_variables with
        | Some idx_formulae ->
          idx_formulae
          |> List.to_seq
          |> Seq.iter (fun (i, f) ->
            VarFormulaGraph.add_edge
              g
              (VarFormulaGraph.V.create (f, v, i))
              (VarFormulaGraph.V.create destination))
        | None -> ()
      in
      let setup formulae =
        let root_idx =
          formulae
          |> List.map (fun f ->
            let min, max = ranges_union (clock_index_ranges f) |> Option.get in
            max - min)
          |> List.argmax_opt Int.compare
          |> Option.get
        in
        let root_formula = List.nth formulae root_idx in
        let coverage_covered =
          formulae
          |> Array.of_list
          |> Array.mapi (fun i f ->
            let coverage = clock_index_ranges f in
            if i = root_idx then f, coverage, coverage else f, coverage, MapOC.empty)
        in
        let _ =
          spawned_variables
          := root_formula
             |> BoolExpr.indexed_vars
             |> List.to_seq
             |> Seq.map (fun (v, i) -> v, [ i, root_idx ])
             |> MapOC.of_seq
        in
        [ root_formula ], coverage_covered
      in
      let equal (before, _) (after, _) =
        if ProductGraph.has_cycle g
        then raise ProductLoop
        else List.length before = List.length after
      in
      let step (product, ranges) =
        let product_covered = clock_index_ranges (And product) in
        let new_spawned_variables = ref MapOC.empty in
        let cover_with fi (f, coverage, covered) =
          let to_consider =
            MapOC.merge
              (fun _key g l ->
                let update (a, b) (c, d) =
                  let left = if a < c then Some (a, c - 1) else None in
                  let right = if d > b then Some (b + 1, d) else None in
                  if Option.is_none left && Option.is_none right
                  then None
                  else Some (Update { left; right })
                in
                match g, l with
                | Some g, Some l -> update g l
                | Some g, None -> Some (Initial g)
                | None, Some _ ->
                  failwith
                    "range saturate, map merge: shouldn't be possible to cover locally \
                     but not globally"
                | None, None -> None)
              product_covered
              covered
          in
          let new_formulae =
            to_consider
            |> MapOC.to_seq
            |> Seq.filter_map (fun (v, cover) ->
              let* min, max = MapOC.find_opt v coverage in
              let diam = max - min in
              let to_cover =
                match cover with
                | Initial (a, b) -> Seq.int_seq_inclusive (a + diam, b)
                | Update { left; right } ->
                  let from_left =
                    match left with
                    | Some (a, b) -> Seq.int_seq_inclusive (a + diam, b + diam)
                    | None -> Seq.empty
                  in
                  let from_right =
                    match right with
                    | Some (c, d) -> Seq.int_seq_inclusive (c, d)
                    | None -> Seq.empty
                  in
                  Seq.append from_left from_right
              in
              Some
                (Seq.map
                   (fun i ->
                     let offset = i - max in
                     let shifted = BoolExpr.shift_by f offset in
                     let new_unshifted_vars =
                       shifted
                       |> BoolExpr.indexed_vars
                       |> List.to_seq
                       |> Seq.filter (fun (v, i) ->
                         not
                           (MapOC.find_opt v product_covered
                            |> Option.fold ~none:false ~some:(fun (l, r) ->
                              l <= i && i <= r)))
                       |> Seq.map (fun (v, i) -> v, i - offset)
                     in
                     let _ =
                       new_unshifted_vars
                       |> Seq.iter (fun (vf, j) ->
                         update_graph v (fi, vf, j);
                         new_spawned_variables
                         := MapOC.entry
                              (fun acc -> (j, fi) :: acc)
                              []
                              !new_spawned_variables
                              vf)
                     in
                     shifted)
                   to_cover))
            |> Seq.concat
            |> List.of_seq
          in
          let update_ranges = clock_index_ranges (And new_formulae) in
          let new_ranges =
            MapOC.union
              (fun _ (a, b) (c, d) -> Some (Int.min a c, Int.max b d))
              covered
              update_ranges
          in
          new_formulae, new_ranges
        in
        let new_formulae, new_ranges = ranges |> Array.mapi cover_with |> Array.split in
        let _ = spawned_variables := !new_spawned_variables in
        ( Seq.append
            (List.to_seq product)
            (new_formulae |> Array.to_seq |> Seq.map List.to_seq |> Seq.concat)
          |> List.of_seq
        , Array.combine ranges new_ranges
          |> Array.map (fun ((f, cov, _), range) -> f, cov, range) )
      in
      let product, _ = fixpoint setup equal step formulae in
      product
  ;;

  let product formulae =
    let components = components_by_vars formulae in
    And (List.concat_map range_saturate components)
  ;;

  (** Returns minimal precondition to inductive step from the given [formulae].*)
  let postcondition product =
    let clock_vars = SetOCI.of_list (BoolExpr.indexed_vars product) in
    let setoci2setci set =
      set
      |> SetOCI.to_seq
      |> Seq.filter_map (fun (c, i) ->
        let* c = c in
        Some (c, i))
      |> SetCI.of_seq
    in
    (*adds c[i]<c[j] relation for clocks; i < j*)
    let logical_filling =
      clock_vars
      |> setoci2setci
      |> logical_clocks_from_vars
      |> Hashtbl.to_seq
      |> Seq.flat_map connect_clocks
      |> List.of_seq
    in
    BoolExpr.use_more_cond (And (product :: logical_filling))
  ;;

  (** Returns basic condition for a logical clock: [0 < c[1]]*)
  let lc_init c = Denotational.Syntax.(Const N.zero < c.@[1])

  (** Returns initial condition for the [product].*)
  let product_init product =
    let norm_reduce_nonzero index f =
      let f = NumExpr.norm_rule f in
      let* f = NumExpr.reduce_zerocond_rule index f in
      Some (NumExpr.norm_rule f)
    in
    let index_to_reduce = 0 in
    let elimination_of_texp_only rule =
      BoolExpr.eliminate (NumExpr.eliminate rule) Option.some
    in
    let use_init_and_simplify =
      elimination_of_texp_only (norm_reduce_nonzero index_to_reduce)
    in
    let remove_sub_zero_refs =
      elimination_of_texp_only (NumExpr.reduce_negative_rule index_to_reduce)
    in
    match ranges_union (clock_index_ranges product) with
    | Some (min, max) ->
      let diameter = max - min in
      let shifted_formulae =
        Seq.int_seq_inclusive (1, diameter + 1)
        (*skip zero because clocks start at 1*)
        |> Seq.filter_map (fun i ->
          let f = BoolExpr.shift_by product i in
          let* f = use_init_and_simplify f in
          remove_sub_zero_refs f)
        |> List.of_seq
      in
      let clocks = product |> BoolExpr.clocks |> List.sort_uniq C.compare in
      let clock_starts = List.map lc_init clocks in
      And (And shifted_formulae :: clock_starts)
    | None -> product
  ;;

  let existence_proof formulae =
    let product = product formulae in
    let post = postcondition product in
    let cond = inductive_step post in
    let pre = precondition post in
    let init = product_init product in
    let init, pre, cond, post = Tuple.map4 BoolExpr.norm (init, pre, cond, post) in
    init, pre, cond, post
  ;;

  let print_proofs (init, pre, ind, post) =
    let init, pre, ind, post = Tuple.map4 Array.to_list (init, pre, ind, post) in
    List.iteri
      (fun i (init, pre, ind, post) ->
        let _ = Printf.printf "Print variant %i:\n" i in
        let _ = Printf.printf "init: %s\n" (string_of_bool_expr init) in
        let _ = Printf.printf "pre: %s\n" (string_of_bool_expr pre) in
        let _ = Printf.printf "ind: %s\n" (string_of_bool_expr ind) in
        let _ = Printf.printf "post: %s\n" (string_of_bool_expr post) in
        ())
      (List.zip4 init pre ind post)
  ;;

  let parameter_names formulae =
    formulae
    |> List.filter_map (function
      | TimeParameter (v, _) | LogicalParameter (v, _) -> Some v
      | _ -> None)
    |> List.sort_uniq C.compare
  ;;

  module Graph = struct
    type 'a vertix =
      | Init of 'a
      | Pre of 'a
      | Step of 'a * 'a
      | Post of 'a
    [@@deriving sexp]

    let vertix_to_string v =
      v |> sexp_of_vertix Sexplib0.Sexp_conv.sexp_of_int |> Sexplib0.Sexp.to_string
    ;;

    type 'f t =
      { init : 'f array
      ; pre : 'f array
      ; ind : 'f array
      ; post : 'f array
      ; edges : (int vertix * int vertix, bool) Hashtbl.t
      ; vertices : (int vertix, bool) Hashtbl.t
      }

    type test =
      | InitPre of int
      | PreStep of int * int
      | StepPost of int * int * int
      | PostPre of int

    type problem =
      | NoSolutions
      | InitIsLast of int
      | PreIsLast of int
      | StepIsLast of int * int

    let report { init; vertices; edges; _ } =
      let len = Array.length init in
      let in_cycle = Hashtbl.create ((len * len) + (2 * len)) in
      let mark_cyclic v = Hashtbl.replace in_cycle v true in
      let visited = Hashtbl.create ((len * len) + (2 * len)) in
      let is_cyclic v = Hashtbl.value in_cycle v false || Hashtbl.mem visited v in
      let visit v = Hashtbl.replace visited v () in
      let next =
        edges
        |> Hashtbl.to_seq
        |> Seq.fold_left
             (fun tbl ((f, t), sat) ->
               if sat then Hashtbl.entry tbl (fun l -> t :: l) f [] else ();
               tbl)
             (Hashtbl.create (Hashtbl.length vertices))
      in
      let rec dfs (v : int vertix) =
        if is_cyclic v
        then (
          visit v;
          mark_cyclic v;
          true, [])
        else (
          visit v;
          let cycles, problems = List.split (List.map dfs (Hashtbl.value next v [])) in
          let problems = List.concat problems in
          if List.any cycles
          then (
            mark_cyclic v;
            true, problems)
          else if List.is_empty problems
          then (
            let p =
              match v with
              | Init i -> InitIsLast i
              | Pre i -> PreIsLast i
              | Step (i, j) -> StepIsLast (i, j)
              | Post _ -> failwith "doesn't make sense for the graph"
            in
            false, [ p ])
          else false, problems)
      in
      let valid_starts, problems =
        init
        |> Array.to_list
        |> List.mapi (fun i _ ->
          if Hashtbl.find vertices (Init i) then dfs (Init i) else false, [])
        |> List.split
      in
      let problems = List.concat problems in
      if not (List.any valid_starts) then NoSolutions :: problems else problems
    ;;
  end

  module Existence = struct
    open Graph

    let bulk_existence_proof formulae =
      formulae
      |> List.map BoolExpr.fact_disj
      |> List.map (List.map BoolExpr.norm)
      |> List.general_cartesian
      |> List.map existence_proof
      |> List.split4
      |> Tuple.map4 Array.of_list
    ;;

    let solve_from_parts (init, pre, ind, post) =
      let len = Array.length init in
      let vertices = Hashtbl.create ((len * len) + (3 * len)) in
      let add_vertex v r = Hashtbl.replace vertices v r in
      let edges = Hashtbl.create (2 * ((len * len) + (3 * len))) in
      let add_arrow from into r = Hashtbl.replace edges (from, into) r in
      let init, pre, ind, post =
        Tuple.map4 (Array.map S.of_formula) (init, pre, ind, post)
      in
      let get = Array.get in
      let steps_by_pre i =
        Seq.int_seq (Array.length ind)
        |> Seq.filter (fun j -> not (Hashtbl.mem edges (Pre i, Step (i, j))))
        |> Seq.map (fun j -> PreStep (i, j))
      in
      let post_inclusions_by_step (i, j) =
        Seq.int_seq (Array.length post)
        |> Seq.filter (fun k ->
          let r = not (Hashtbl.mem edges (Step (i, j), Post k)) in
          r)
        |> Seq.map (fun k -> StepPost (i, j, k))
      in
      let test_queue = ref (Array.to_seq (Array.mapi (fun i _ -> InitPre i) init)) in
      let process q =
        q
        |> Seq.flat_map (function
          | InitPre i ->
            let sat = S.sat (get init i) in
            let _ = add_vertex (Init i) sat in
            if sat
            then (
              let sat = S.sat (get pre i) in
              let _ = add_vertex (Pre i) sat in
              if sat
              then (
                add_arrow (Init i) (Pre i) sat;
                steps_by_pre i)
              else Seq.empty)
            else Seq.empty
          | PreStep (p, i) ->
            let pre = get pre p in
            let ind = get ind i in
            let step = S.(pre && ind) in
            let sat = S.sat step && S.infinite_in S.index_name step in
            let includes = S.(more_precise pre step) in
            let _ =
              add_arrow (Pre p) (Step (p, i)) includes;
              add_vertex (Step (p, i)) sat
            in
            if sat && includes then post_inclusions_by_step (p, i) else Seq.empty
          | StepPost (i, j, k) ->
            let pre = get pre i in
            let ind = get ind j in
            let post = get post k in
            let step = S.(pre && ind) in
            let sat = S.sat post in
            let includes = S.(step <= post) in
            let _ =
              add_arrow (Step (i, j)) (Post k) includes;
              add_vertex (Post k) sat
            in
            if sat && includes && not (Hashtbl.mem edges (Post k, Pre k))
            then Seq.return (PostPre k)
            else Seq.empty
          | PostPre i ->
            let sat = S.sat (get pre i) in
            let _ =
              add_vertex (Pre i) sat;
              add_arrow (Post i) (Pre i) sat
            in
            if sat then steps_by_pre i else Seq.empty)
        |> List.of_seq
        |> List.to_seq
      in
      let _ =
        while not (Seq.is_empty !test_queue) do
          test_queue := process !test_queue
        done
      in
      { init; pre; ind; post; edges; vertices }
    ;;

    type solution =
      | Trivial (** Solution is [Trivial] when there are no constraints. *)
      | Proof of S.t Graph.t * problem list

    let solve_expr formulae =
      if List.is_empty formulae
      then Trivial
      else (
        let proofs = bulk_existence_proof formulae in
        let solution = solve_from_parts proofs in
        Proof (solution, report solution))
    ;;

    type report =
      | Exact of solution
      | Approximation of
          { over : solution
          ; under : solution option
          }

    let print_solution_graph = function
      | Trivial -> ()
      | Proof (g, _) ->
        let print =
          Array.iteri (fun i d -> Printf.printf "%i:\n%s\n" i (S.to_string d))
        in
        Printf.printf "Inits:\n";
        print g.init;
        Printf.printf "Pres:\n";
        print g.pre;
        Printf.printf "Inds:\n";
        print g.ind;
        Printf.printf "Posts:\n";
        print g.post
    ;;

    let print_report_graph = function
      | Exact sol -> print_solution_graph sol
      | Approximation { over; under } ->
        Printf.printf "OVERAPPROXIMATION:\n";
        print_solution_graph over;
        Printf.printf "UNDERAPPROXIMATION:\n";
        Option.iter print_solution_graph under
    ;;

    let solution_is_correct = function
      | Trivial -> true
      | Proof (_, problems) -> List.is_empty problems
    ;;

    let report_is_correct = function
      | Exact solution -> solution_is_correct solution
      | Approximation { over; _ } -> solution_is_correct over
    ;;

    let solution_exists = function
      | Exact solution -> solution_is_correct solution
      | Approximation { under; _ } ->
        Option.fold ~none:false ~some:solution_is_correct under
    ;;

    let solve spec =
      let exact_formulae = safe_exact_rel_spec spec in
      match exact_formulae with
      | Some formulae -> Exact (solve_expr formulae)
      | None ->
        let over_formulae = over_rel_priority_exact_spec spec in
        let over = solve_expr over_formulae in
        let under_formulae = safe_under_rel_priority_exact_spec spec in
        let under = Option.map solve_expr under_formulae in
        Approximation { over; under }
    ;;

    let print_problems g problems =
      let pre i = Array.get g.pre i in
      let ind i = Array.get g.ind i in
      let post i = Array.get g.post i in
      let str_pre i = S.to_string (pre i) in
      let str_ind i = S.to_string (ind i) in
      let str_post i = S.to_string (post i) in
      S.set_debug true;
      let print = function
        | NoSolutions -> Printf.printf "No infinite cycles.\n"
        | InitIsLast i -> Printf.printf "Precondition is empty: %s\n" (str_pre i)
        | PreIsLast i ->
          Array.iteri
            (fun j dom ->
              if S.sat dom
              then
                Printf.printf
                  "Non-empty unreachable step %i:\n\
                   Infinite in index: %b\n\
                   Strictily expands precondition: %b\n\
                   Pre %i:\n\
                   %s\n\
                   Ind %i:\n\
                   %s\n\
                   Both:\n\
                   %s\n"
                  j
                  (S.infinite_in S.index_name dom)
                  S.(more_precise (pre i) (pre i && ind j))
                  i
                  (str_pre i)
                  j
                  (str_ind j)
                  S.(to_string (pre i && ind j))
              else Printf.printf "Empty step: %i %i\n" i j)
            g.ind
        | StepIsLast (i, j) ->
          Array.iteri
            (fun k dom ->
              if S.sat dom
              then (
                Printf.printf
                  "Non-empty unreachable post: %i %i % i\n\
                   pre:\n\
                   %s\n\
                   ind:\n\
                   %s\n\
                   post:\n\
                   %s\n\
                   <= is %b\n\
                   diff:\n"
                  i
                  j
                  k
                  (str_pre i)
                  (str_ind j)
                  (str_post k)
                  S.((pre i && ind j) <= post k);
                List.iter
                  (print_endline << S.to_string)
                  S.(diff (pre i && ind j) (post k)))
              else Printf.printf "Empty post: %i\n" k)
            g.post
      in
      if List.is_empty problems
      then Printf.printf "No problems\n"
      else List.iter print problems;
      S.set_debug false
    ;;

    let print_solution = function
      | Trivial -> Printf.printf "Specification is trivially correct.\n"
      | Proof (g, problems) -> print_problems g problems
    ;;

    let print = function
      | Exact solution -> print_solution solution
      | Approximation { over; under } ->
        Printf.printf "OVERAPPROXIMATION:\n";
        print_solution over;
        Printf.printf "UNDERAPPROXIMATION:\n";
        (match under with
         | Some under -> print_solution under
         | None -> Printf.printf "Doesn't exist.")
    ;;

    let extract_params param_vars =
      let from_graph { init; pre; ind; post; vertices; edges } =
        let next =
          edges
          |> Hashtbl.to_seq
          |> Seq.fold_left
               (fun tbl ((f, t), sat) ->
                 if sat then Hashtbl.entry tbl (fun l -> t :: l) f [] else ();
                 tbl)
               (Hashtbl.create (Hashtbl.length vertices))
        in
        let rec dfs (v : int vertix) prev_params prev_vertices =
          if not (Hashtbl.find vertices v)
          then []
          else if List.mem v prev_vertices
          then [ prev_params ]
          else (
            let dom =
              match v with
              | Init i -> init.(i)
              | Pre i -> pre.(i)
              | Step (i, j) -> S.(pre.(i) && ind.(j))
              | Post i -> post.(i)
            in
            let params = S.(prev_params && project param_vars dom) in
            let next_vertices = Hashtbl.value next v [] in
            List.flat_map (fun nv -> dfs nv params (v :: prev_vertices)) next_vertices)
        in
        init
        |> Array.to_seq
        |> Seq.mapi (fun i _ ->
          if Hashtbl.find vertices (Init i)
          then dfs (Init i) (S.of_formula (And [])) []
          else [])
        |> Seq.map List.to_seq
        |> Seq.concat
        |> List.of_seq
      in
      let from_solution = function
        | Trivial -> [ S.of_formula (And []) ]
        | Proof (graph, _) -> from_graph graph
      in
      function
      | Exact sol -> from_solution sol
      | Approximation { over; under } ->
        let params = from_solution over in
        (match under with
         | Some under ->
           List.cartesian params (from_solution under)
           |> List.map (fun (l, r) -> S.(l && r))
         | None -> params)
    ;;
  end

  module Simulation = struct
    open Graph

    type var_family =
      | Free of C.t
      | Clock of C.t
      | Index
    [@@deriving compare]

    module VarFamilySet = Set.Make (struct
        type t = var_family

        let compare = compare_var_family
      end)

    let remove_by_var_rule vars = function
      | Var v ->
        let* v =
          match v with
          | FreeVar v when VarFamilySet.mem (Free v) vars -> None
          | ClockVar (c, _) when VarFamilySet.mem (Clock c) vars -> None
          | Index _ when VarFamilySet.mem Index vars -> None
          | _ -> Some v
        in
        Some (Var v)
      | _ as e -> Some e
    ;;

    let eliminate_by_clocks vars formula =
      BoolExpr.eliminate (remove_by_var_rule vars) Option.some formula
      |> Option.value ~default:(And [])
    ;;

    let remove_by_match_rule constraints f =
      match f with
      | Linear _ ->
        let to_match =
          match ranges_union (clock_index_ranges f) with
          | Some (_, max) ->
            let shifted = BoolExpr.shift_by f (-max) in
            shifted
          | None -> f
        in
        if ExprSet.mem to_match constraints then None else Some f
      | _ -> Some f
    ;;

    let remove_matching to_remove formula =
      BoolExpr.eliminate Option.some (remove_by_match_rule to_remove) formula
      |> Option.value ~default:(And [])
    ;;

    (** [enum_specialized] enumerates specialized versions of the formula [f]: for initial condition and for the non initial (split by zero cond).*)
    let enum_specialized f =
      BoolExpr.use_more_cond f :: Option.to_list (BoolExpr.eliminate_zerocond 0 f)
    ;;

    let remove_sticking_connectors f =
      let* core =
        BoolExpr.eliminate
          Option.some
          (function
            | Linear (Var (ClockVar (c1, i)), Less, Var (ClockVar (c2, j)))
              when C.compare c1 c2 = 0 && i = j - 1 -> None
            | e -> Some e)
          f
      in
      let ranges = clock_index_ranges core in
      BoolExpr.eliminate
        (function
          | Var (ClockVar (c, i)) as e ->
            let min, max = MapOC.find (Some c) ranges in
            if min <= i && i <= max then Some e else None
          | e -> Some e)
        Option.some
        f
    ;;

    module SubstituteMap = Map.Make (C)

    let rec equalities acc = function
      | Linear (Var (ClockVar (l, i)), Eq, Var (ClockVar (r, j))) ->
        ((l, i), (r, j)) :: acc
      | Linear _ -> acc
      | And list | Or list -> List.fold_left equalities acc list
    ;;

    module VarSet = Set.Make (C)

    let equalities_to_substitution eqs except =
      List.fold_left
        (fun map ((l, i), (r, j)) ->
          let maybe_add (l, i) (r, j) map =
            if not (VarSet.mem l except) then SubstituteMap.add l (r, j - i) map else map
          in
          let map = maybe_add (l, i) (r, j) map in
          maybe_add (r, j) (l, i) map)
        SubstituteMap.empty
        eqs
    ;;

    let substitute map f =
      BoolExpr.rewrite
        (function
          | Var (ClockVar (c, i)) as e ->
            SubstituteMap.find_opt c map
            |> Option.map (fun (sub, j) -> Var (ClockVar (sub, i + j)))
            |> Option.value ~default:e
          | e -> e)
        Fun.id
        f
    ;;

    (** [remove_difference] returns proof obligations without constraints that are in [p] but not in [s]*)
    let remove_difference parts s p =
      (* When property introduces equalities, we may remove more than we should. For this we need to renormalize with these new equalities. *)
      let property_equalities = List.fold_left equalities [] p in
      let struct_vars =
        List.fold_left
          (BoolExpr.fold_vars (fun v set ->
             match v with
             | ClockVar (c, _) -> VarSet.add c set
             | _ -> set))
          VarSet.empty
          s
      in
      let substition = equalities_to_substitution property_equalities struct_vars in
      let parts = Tuple.map4 (Array.map (substitute substition)) parts in
      let p = List.map (substitute substition) p in
      let constraint_set formulae =
        formulae
        |> List.to_seq
        |> Seq.flat_map (List.to_seq << BoolExpr.fact_disj)
        |> Seq.flat_map (List.to_seq << enum_specialized)
        |> Seq.flat_map (List.to_seq << BoolExpr.flatten << BoolExpr.norm)
        |> Seq.map (fun f ->
          match BoolExpr.max_index_opt f with
          | Some max -> BoolExpr.shift_by f (-max)
          | None -> f)
        |> ExprSet.of_seq
      in
      let struct_exprs = constraint_set s in
      let property_exprs = constraint_set p in
      let diff_constraints = ExprSet.diff property_exprs struct_exprs in
      let remove_diff_exprs = remove_matching diff_constraints in
      let var_families formulae =
        List.fold_left
          (fun acc f ->
            let seq =
              f
              |> BoolExpr.vars
              |> List.to_seq
              |> Seq.map (function
                | FreeVar v -> Free v
                | ClockVar (c, _) -> Clock c
                | Index _ -> Index)
            in
            VarFamilySet.add_seq seq acc)
          VarFamilySet.empty
          formulae
      in
      let struct_vars = var_families s in
      let property_vars = var_families p in
      let diff_vars = VarFamilySet.diff property_vars struct_vars in
      let remove_diff_vars = eliminate_by_clocks diff_vars in
      let general_remove = remove_diff_vars << remove_diff_exprs << BoolExpr.norm in
      let init, pre, ind, post =
        Tuple.map4
          (Array.map (Option.get << remove_sticking_connectors << general_remove))
          parts
      in
      let index_to_reduce = 0 in
      let elimination_of_texp_only rule =
        BoolExpr.eliminate (NumExpr.eliminate rule) Option.some
      in
      let remove_sub_zero_refs =
        elimination_of_texp_only (NumExpr.reduce_negative_rule index_to_reduce)
      in
      let init = Array.map (fun f -> remove_sub_zero_refs f |> Option.get) init in
      let pre = Array.map (Option.get << remove_sticking_connectors) pre in
      let ind = Array.map (fun f -> inductive_step f) ind in
      init, pre, ind, post
    ;;

    let simulate (s : S.t t) (sp : S.t t) =
      let get = Array.get in
      let init = Array.combine s.init sp.init in
      let pre = Array.combine s.pre sp.pre in
      let ind = Array.combine s.ind sp.ind in
      let post = Array.combine s.post sp.post in
      let check (s, sp) = S.more_precise s sp in
      let vertices =
        s.vertices
        |> Hashtbl.to_seq
        |> Seq.map (fun (v, _) ->
          let sat =
            match v with
            | Init i -> check (get init i)
            | Pre i -> check (get pre i)
            | Step (i, j) ->
              let s_pre, sp_pre = get pre i in
              let s_ind, sp_ind = get ind j in
              check S.(s_pre && s_ind, sp_pre && sp_ind)
            | Post i -> check (get post i)
          in
          v, sat)
        |> Hashtbl.of_seq
      in
      let edges =
        s.edges
        |> Hashtbl.to_seq
        |> Seq.map (fun ((f, t), sat) ->
          let sat = sat && Hashtbl.find vertices t in
          (f, t), sat)
        |> Hashtbl.of_seq
      in
      { init; pre; ind; post; edges; vertices }
    ;;

    let solve_expr s p =
      (*S /\ P*)
      let sp_parts = Existence.bulk_existence_proof (s @ p) in
      let sp_solution = Existence.solve_from_parts sp_parts in
      (*(S /\ P) \ P*)
      let s_parts = remove_difference sp_parts s p in
      let s_solution = Existence.solve_from_parts s_parts in
      let simulation_relation = simulate s_solution sp_solution in
      s_solution, sp_solution, simulation_relation
    ;;

    let report (s, sp, sim) = report s, report sp, report sim

    let print_problems
      ((a_sol, a_problems), (ab_sol, ab_problems), (sim_sol, sim_problems))
      =
      let _ =
        Printf.printf "A EXISTENCE PROBLEMS:\n";
        Existence.print_problems a_sol a_problems;
        Printf.printf "AB EXISTENCE PROBLEMS:\n";
        Existence.print_problems ab_sol ab_problems;
        Printf.printf "SIMULATION PROBLEMS:\n"
      in
      S.set_debug true;
      let print = function
        | NoSolutions ->
          Printf.printf "No valid simulation at all\n";
          Array.iter
            (fun (x, y) ->
              let sat = S.more_precise x y in
              if not sat
              then
                Printf.printf
                  "Failed init:\nmore precise: %b\n%s\n%s\n"
                  sat
                  (S.to_string x)
                  (S.to_string y))
            sim_sol.init
        | InitIsLast i ->
          let f, t = Array.get sim_sol.init i in
          Printf.printf
            "------INIT------\n%s\nDOES NOT SIMULATE\n%s\n"
            (S.to_string f)
            (S.to_string t)
        | PreIsLast i ->
          Printf.printf
            "Precondition %i is %s and doesn't have valid simulated steps\n"
            i
            (Tuple.to_string2 (Bool.to_string << S.sat) sim_sol.pre.(i));
          Array.iteri
            (fun j (l, r) ->
              Printf.printf
                "Unreachable step %i:\n\
                 Strictily expands precondition: %b\n\
                 L:\n\
                 %s\n\
                 R:\n\
                 %s\n"
                j
                S.(more_precise l r)
                (S.to_string l)
                (S.to_string r))
            sim_sol.ind
        | StepIsLast (i, j) ->
          Printf.printf "Step %i %i doesn't lead to valid simulated postconditions\n" i j
      in
      if List.is_empty sim_problems
      then Printf.printf "No problems\n"
      else List.iter print sim_problems;
      S.set_debug false
    ;;

    type solution =
      | Trivial
      | Proof of
          (S.t Graph.t * problem list)
          * (S.t Graph.t * problem list)
          * ((S.t * S.t) Graph.t * problem list)

    let solve trivial a b =
      let solve_expr a_formulae b_formulae =
        if trivial a_formulae b_formulae
        then Trivial
        else (
          let a, ab, sim = solve_expr a_formulae b_formulae in
          let a_p, ab_p, sim_p = report (a, ab, sim) in
          Proof ((a, a_p), (ab, ab_p), (sim, sim_p)))
      in
      let* a = safe_under_rel_priority_exact_spec a in
      let* b = safe_under_rel_priority_exact_spec b in
      Some (solve_expr a b)
    ;;

    let solution_exists = function
      | Trivial -> true
      | Proof ((_, a_p), (_, ab_p), (_, sim_p)) ->
        List.is_empty a_p && List.is_empty ab_p && List.is_empty sim_p
    ;;

    let print = function
      | Trivial -> Printf.printf "Simulation is trivially correct.\n"
      | Proof (a, b, sim) -> print_problems (a, b, sim)
    ;;
  end

  module Assumption = struct
    (** Solution is [Trivial] when assumption is empty. *)
    let solve = Simulation.solve (fun a _s -> List.is_empty a)
  end

  module Property = struct
    (** Solution is [Trivial] when property is empty. *)
    let solve = Simulation.solve (fun _s p -> List.is_empty p)
  end

  module Module = struct
    type report =
      { assumption : Existence.report
      ; structure : Existence.report
      ; property : Existence.report
      ; assumption_in_structure : Simulation.solution option
      ; structure_in_property : Simulation.solution option
      }

    let solve (a, s, p) =
      { assumption = Existence.solve a
      ; structure = Existence.solve (a @ s)
      ; property = Existence.solve p
      ; assumption_in_structure = Assumption.solve a s
      ; structure_in_property = Property.solve (a @ s) p
      }
    ;;

    let is_correct
      { assumption; structure; property; assumption_in_structure; structure_in_property }
      =
      Existence.solution_exists assumption
      && Existence.solution_exists structure
      && Existence.solution_exists property
      && Option.fold ~some:Simulation.solution_exists ~none:false assumption_in_structure
      && Option.fold ~some:Simulation.solution_exists ~none:false structure_in_property
    ;;

    let print r =
      let { assumption
          ; structure
          ; property
          ; assumption_in_structure
          ; structure_in_property
          }
        =
        r
      in
      if is_correct r
      then Printf.printf "The module is proven correct in infinite subset."
      else (
        Printf.printf "A:\n";
        Existence.print assumption;
        Printf.printf "A+S:\n";
        Existence.print structure;
        (let print = function
           | Existence.Trivial -> ()
           | Existence.Proof (g, _) -> Printf.printf "%s\n" (S.to_string g.post.(0))
         in
         match structure with
         | Existence.Exact sol -> print sol
         | Existence.Approximation { over; under } ->
           print over;
           Option.iter print under);
        Printf.printf "P:\n";
        Existence.print property;
        Printf.printf "A in (A and S):\n";
        (match assumption_in_structure with
         | None -> Printf.printf "Under-approximation doesn't exist."
         | Some a -> Simulation.print a);
        Printf.printf "(A and S) in (A and S and P):\n";
        match structure_in_property with
        | None -> Printf.printf "Under-approximation doesn't exist."
        | Some p -> Simulation.print p)
    ;;
  end
end

module MakeWithDomain
    (V : Var)
    (N : sig
       include Num
       include Domain.Num with type t := t
     end)
    (D : Solver.D with type v = V.t and type n = N.t) =
struct
  module S = Solver.MakeFromDomain (V) (N) (D)
  include Make (V) (N) (S)
end

module Test
    (MakeDomain : functor
       (V : Var)
       (N : sig
          include Num
          include Domain.Num with type t := t
        end)
       -> Domain.S with type v = V.t and type n = N.t) =
struct
  module N = struct
    include Number.Rational

    let to_rational = Fun.id
  end

  module D = struct
    include MakeDomain (String) (N)

    let index_name = "i"
  end

  module P = struct
    include Denotational.MakeDebug (String) (N)
    include MakeWithDomain (String) (N) (D)

    let to_polyhedra index_name formula =
      let formula = Denotational.BoolExpr.logical_norm formula in
      D.add_constraint
        index_name
        (D.top index_name (Denotational.BoolExpr.unique_vars String.compare formula))
        formula
    ;;
  end

  let%test_unit _ = assert (D.is_top (P.to_polyhedra "i" (And [])))
  let%test_unit _ = assert (not @@ D.is_bottom (P.to_polyhedra "i" (And [])))

  let%test_unit _ =
    let c = Rtccsl.Precedence { cause = "a"; effect = "b" } in
    let formula = P.exact_rel c in
    let domain = P.to_polyhedra "i" formula in
    assert (not @@ D.is_bottom domain)
  ;;
end

let%test_module _ =
  (module struct
    include Test (Domain.Polka (struct
        type dom = Polka.loose Polka.t

        let alloc = Polka.manager_alloc_loose ()
      end))
  end)
;;

let%test_module _ =
  (module struct
    include Test (Domain.VPL)
  end)
;;
