open Prelude

module type Var = sig
  open Interface
  include OrderedType
  include Interface.Debug with type t := t
end

module type Num = sig
  include Interface.OrderedType
  include Interface.Number.Field with type t := t
  include Interface.Debug with type t := t
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

    include Interface.Stringable with type t := t
  end

  module type D = sig
    include Domain.S

    val index_name : v
  end

  module MakeFromDomain
      (V : Var)
      (N : sig
         type t

         val to_rational : t -> Number.Rational.t
       end)
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
  open Denotational
  open Rtccsl
  open MakeDebug (C) (N)

  module N = struct
    include N
    include Interface.ExpOrder.Make (N)
  end

  open MakeExpr (N)

  type expr = (C.t, N.t) bool_expr

  exception ExactRelationUnavailable
  exception OverApproximationUnavailable
  exception UnderApproximationUnavailable

  (** Returns exact semi-linear denotational relation of a RTCCSL constraint. Raises [ExactRelationUnavailable] otherwise.*)
  let exact_rel c =
    let open Syntax in
    let i = 0 in
    (*dummy variable*)
    match c with
    | Precedence { cause; effect } -> cause @ i < effect @ i
    | Causality { cause; effect } -> cause @ i <= effect @ i
    | RTdelay { out; arg; delay = e1, e2 } -> (out @ i) - (arg @ i) |> (Const e1, Const e2)
    | Delay { out; arg; delay = d1, d2; base = None } when Stdlib.(d1 = d2) ->
      (arg @ Stdlib.(i - d1)) = out @ i
    | Fastest { out; left; right } -> out @ i = min (left @ i) (right @ i)
    | Slowest { out; left; right } -> out @ i = max (left @ i) (right @ i)
    | CumulPeriodic { out; period; error = le, re; offset } ->
      let prev = ZeroCond ((out @ Stdlib.(i - 1)), offset) in
      (out @ i) - prev |> N.(Const (period + le), Const (period + re))
    | AbsPeriodic { out; period; error = le, re; offset } ->
      (out @ i) - (Const period * Index Stdlib.(i - 1)) - Const offset
      |> (Const le, Const re)
    | Sporadic { out; at_least; strict } ->
      let diff = (out @ i) - (out @ Stdlib.(i - 1)) in
      let at_least = Const at_least in
      if strict then diff > at_least else diff >= at_least
    | _ -> raise ExactRelationUnavailable
  ;;

  let exact_spec (s : ('c, 'n) specification) : ('c, 'n) bool_expr list =
    List.map exact_rel s
  ;;

  (** Returns overapproximation denotational relation of a RTCCSL constraint. Raises [OverApproximationUnavailable] otherwise.*)
  let over_rel c =
    try exact_rel c with
    | ExactRelationUnavailable ->
      let open Syntax in
      let i = 0 in
      (match c with
       | FirstSampled { out; arg; base } | LastSampled { out; arg; base } ->
         let _ = arg in
         (base @ Stdlib.(i - 1)) < out @ i && out @ i <= base @ i
       | _ -> raise OverApproximationUnavailable)
  ;;

  let over_rel_spec spec = List.map over_rel spec

  (** [safe_ver_rel c] returns overapproximation defined in [over_rel] or empty rel (always valid overapproximation).*)
  let safe_over_rel c =
    try over_rel c with
    | OverApproximationUnavailable ->
      let clocks = Rtccsl.clocks c in
      And (List.map (fun c -> Syntax.(Const N.zero < c @ 0)) clocks)
  ;;

  let safe_over_rel_spec spec = List.map safe_over_rel spec

  (** [under_rel c] returns underapproximation denotational relation of [c] constraint. Raises [UnderApproximationUnavailable] if doesn't exist.*)
  let under_rel c =
    try exact_rel c with
    | ExactRelationUnavailable ->
      let open Syntax in
      let i = 0 in
      (match c with
       | FirstSampled { out; arg; base } | LastSampled { out; arg; base } ->
         let _ = arg in
         (base @ Stdlib.(i - 1)) < out @ i && out @ i = arg @ i && arg @ i <= base @ i
       | Sample { out; arg; base } ->
         out @ i = base @ i
         && arg @ i |> (ZeroCond ((base @ Stdlib.(i - 1)), N.zero), base @ i)
       | _ -> raise UnderApproximationUnavailable)
  ;;

  let under_rel_spec spec = List.map under_rel spec
  let lc_connection c i = Denotational.Syntax.((c @ Stdlib.(i - 1)) < c @ i)

  module SetCI = Set.Make (struct
      type t = C.t * int

      let compare (c1, i1) (c2, i2) =
        let comp = C.compare c1 c2 in
        if comp = 0 then Int.compare i1 i2 else comp
      ;;
    end)

  (**Intersects all [formulae] with logical clocks related to their past.*)
  let inductive_step formulae =
    let unique_num_vars =
      formulae
      |> List.to_seq
      |> Seq.flat_map (fun f -> f |> BoolExpr.vars_except_i |> List.to_seq)
      |> SetCI.of_seq
      |> SetCI.elements
    in
    let connections_to_past = List.map (Tuple.fn2 lc_connection) unique_num_vars in
    And (And (List.map BoolExpr.use_more_cond formulae) :: connections_to_past)
  ;;

  module MapOCMM = Map.Make (struct
      type t = C.t option

      let compare = Option.compare C.compare
    end)

  let clock_index_ranges formula =
    let rule c i acc =
      let l, r = MapOCMM.find_opt c acc |> Option.value ~default:(i, i) in
      MapOCMM.add c Int.(min i l, max i r) acc
    in
    BoolExpr.fold rule MapOCMM.empty formula
  ;;

  let ranges_union r =
    let reduce _ (lmin, lmax) = function
      | Some (gmin, gmax) -> Some (Int.min lmin gmin, Int.max lmax gmax)
      | None -> Some (lmin, lmax)
    in
    MapOCMM.fold reduce r None |> Option.get
  ;;

  (** Construsts inductive precondition from postcondition [post].*)
  let precondition post = BoolExpr.map_idx (fun _ i -> i - 1) post

  module SetOCI = Set.Make (struct
      type t = C.t option * int

      let compare (c1, i1) (c2, i2) =
        let comp = Option.compare C.compare c1 c2 in
        if comp = 0 then Int.compare i1 i2 else comp
      ;;
    end)

  (** Multiplies two formulae using fixpoint saturation.*)
  let mul l r =
    let livars = BoolExpr.indexed_vars l in
    let rivars = BoolExpr.indexed_vars r in
    let make_shift_table ivars =
      List.fold_left
        (fun tbl (c, i) ->
          Hashtbl.entry tbl (fun prev -> Int.min prev i) c i;
          tbl)
        (Hashtbl.create 16)
        ivars
    in
    let shift_lvars = make_shift_table livars in
    let shift_rvars = make_shift_table rivars in
    let saturate_one f shift_vars to_visit =
      let formulae, visited =
        to_visit
        |> SetOCI.to_seq
        |> Seq.filter_map (fun (c, i) ->
          let* offset_in_f = Hashtbl.find_opt shift_vars c in
          let offset = i - offset_in_f in
          if offset <= 0
          then (
            let shifted = BoolExpr.shift_by f offset in
            Some (shifted, (c, i)))
          else None)
        |> List.of_seq
        |> List.split
      in
      formulae, SetOCI.of_list visited
    in
    let saturation_step (prev, visited_by_l, visited_by_r) =
      let new_ls, new_lvisits =
        saturate_one l shift_lvars (SetOCI.diff visited_by_r visited_by_l)
      in
      let new_rs, new_rvisits =
        saturate_one r shift_rvars (SetOCI.diff visited_by_l visited_by_r)
      in
      ( And (And (prev :: new_ls) :: new_rs)
      , SetOCI.union visited_by_l new_lvisits
      , SetOCI.union visited_by_r new_rvisits )
    in
    let f, _, _ =
      fixpoint
        (fun () -> And [ l; r ], SetOCI.of_list livars, SetOCI.of_list rivars)
        (fun (_, a, b) (_, c, d) -> SetOCI.equal a c && SetOCI.equal b d)
        saturation_step
        ()
    in
    f
  ;;

  (** Forms a formula hull from stateful (past-referencing) formulae, returns the hull and all statelss formulae.*)
  let stateful_hull formulae =
    let stateful, stateless = List.partition BoolExpr.is_stateful formulae in
    let product =
      match stateful with
      | [] -> And []
      | x :: [] -> x
      | f :: tail -> List.fold_left mul f tail
    in
    product, stateless
  ;;

  (** Returns minimal precondition to inductive step from the given [formulae].*)
  let postcondition formulae =
    let hull, stateless = stateful_hull formulae in
    let hull_vars = SetOCI.of_list (BoolExpr.indexed_vars hull) in
    let stateless_vars =
      stateless
      |> List.map (List.to_seq << BoolExpr.indexed_vars)
      |> List.to_seq
      |> Seq.concat
    in
    let present_vars = SetOCI.add_seq stateless_vars hull_vars in
    let present_indices =
      present_vars
      |> SetOCI.to_seq
      |> Seq.map (fun (_, i) -> i)
      |> List.of_seq
      |> List.sort_uniq Int.compare
    in
    let stateless_with_vars =
      List.map (fun f -> f, SetOCI.of_list (BoolExpr.indexed_vars f)) stateless
    in
    let shift_if_present ((f, vars), i) =
      let shifted_vars = SetOCI.map (fun (c, j) -> c, j + i) vars in
      if SetOCI.subset shifted_vars vars (*all variables should be present in the hull*)
      then Some (BoolExpr.map_idx (fun _ i -> i) f)
      else None
    in
    let constraint_filling =
      Seq.product (List.to_seq stateless_with_vars) (List.to_seq present_indices)
      (*product of stateless with indices is to not go though the same indices several times, which can happen in case of using all present variables*)
      |> Seq.filter_map shift_if_present
      |> List.of_seq
    in
    let logical_clocks =
      SetOCI.fold
        (fun (c, i) tbl ->
          match c with
          | Some c ->
            Hashtbl.entry tbl (fun list -> i :: list) c [];
            tbl
          | None -> tbl)
        present_vars
        (Hashtbl.create 32)
    in
    let rec connect_indices c = function
      | [] | _ :: [] -> []
      | x :: y :: tail ->
        Denotational.Syntax.(c @ x < c @ y) :: connect_indices c (y :: tail)
    in
    let connect_clocks (c, indices) =
      let indices = List.fast_sort Int.compare indices in
      List.to_seq (connect_indices c indices)
    in
    (*adds c[i]<c[j] relation for clocks; i < j*)
    let logical_filling =
      logical_clocks |> Hashtbl.to_seq |> Seq.flat_map connect_clocks |> List.of_seq
    in
    BoolExpr.use_more_cond (And (And (hull :: constraint_filling) :: logical_filling))
  ;;

  (** Returns basic condition for a logical clock: [0 < c[1]]*)
  let lc_init c = Denotational.Syntax.(Const N.zero < c @ 1)

  (** Returns initial condition for the [formulae] of the given [width].*)
  let init_cond width formulae =
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
    let shifted_formulae =
      Seq.product (List.to_seq formulae) (Seq.int_seq_inclusive (1, width))
      (*skip zero because clocks start at 1*)
      |> Seq.filter_map (fun (f, i) ->
        let f = BoolExpr.shift_by f i in
        (* let _ = Printf.printf "bf: %s\n" (string_of_bool_expr f) in *)
        let* f = use_init_and_simplify f in
        (* let _ = Printf.printf "af: %s\n" (string_of_bool_expr f) in *)
        remove_sub_zero_refs f)
      |> List.of_seq
    in
    let vars =
      formulae |> List.flat_map BoolExpr.vars |> List.flat |> List.sort_uniq C.compare
    in
    let clock_starts = List.map lc_init vars in
    let clock_connections =
      Seq.product (List.to_seq vars) (Seq.int_seq_inclusive (2, width))
      (*skip zero and first because they are handled before*)
      |> Seq.map (fun (c, i) -> lc_connection c i)
      |> List.of_seq
    in
    And (And (And shifted_formulae :: clock_connections) :: clock_starts)
  ;;

  let existence_proof formulae =
    let post = postcondition formulae in
    let cond = inductive_step formulae in
    let pre = precondition post in
    let min_index, _ = ranges_union (clock_index_ranges post) in
    let width = -min_index + 1 in
    let init = init_cond width formulae in
    let init, pre, cond, post = Tuple.map4 BoolExpr.norm (init, pre, cond, post) in
    let _ = Printf.printf "existence proof:\n" in
    let _ = Printf.printf "init: %s\n" (string_of_bool_expr init) in
    let _ = Printf.printf "pre: %s\n" (string_of_bool_expr pre) in
    let _ = Printf.printf "step: %s\n" (string_of_bool_expr cond) in
    let _ = Printf.printf "post: %s\n" (string_of_bool_expr post) in
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
    (* let _ =
       Hashtbl.iter
       (fun v sat -> Printf.printf "%s: %b\n" (vertix_to_string v) sat)
       vertices
       in
       let _ =
       Hashtbl.iter
       (fun (f, t) sat ->
       Printf.printf "%s -> %s: %b\n" (vertix_to_string f) (vertix_to_string t) sat)
       edges
       in *)
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
    (* let print_marks m =
       Hashtbl.iter
       (fun k v ->
       match k with
       | Pre i -> Printf.printf "pre %i: %b\n" i v
       | Step (i, j) -> Printf.printf "step %i %i: %b\n" i j v
       | Post i -> Printf.printf "post %i: %b\n" i v)
       m
       in *)
    (* let _ = print_marks marks in *)
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

  (*TODO: modify the function to print pairs too.*)
  let print_problems g problems =
    let pre i = Array.get g.pre i in
    let ind i = Array.get g.ind i in
    let post i = Array.get g.post i in
    let str_pre i = S.to_string (pre i) in
    let str_ind i = S.to_string (ind i) in
    let str_post i = S.to_string (post i) in
    let print = function
      | NoSolutions -> Printf.printf "No solutions, all inits are empty\n"
      | InitIsLast i -> Printf.printf "Precondition is empty: %s\n" (str_pre i)
      | PreIsLast i ->
        Array.iteri
          (fun j dom ->
            if S.sat dom
            then
              Printf.printf
                "Non-empty unreachable step:\n\
                 Infinite in index: %b\n\
                 Pre %i:\n\
                 %s\n\
                 Ind %i:\n\
                 %s\n\
                 Both:\n\
                 %s\n\
                 Diff:\n\
                 %s\n"
                (S.infinite_in S.index_name dom)
                i
                (str_pre i)
                j
                (str_ind j)
                S.(to_string (pre i && ind j))
                ""
            else Printf.printf "Empty step: %i %i\n" i j)
          g.ind
      | StepIsLast (i, j) ->
        Array.iteri
          (fun k dom ->
            if S.sat dom
            then
              Printf.printf
                "Non-empty unreachable post: %i %i % i\npre:\n%s\nind:\n%s\npost:\n%s\n%b"
                i
                j
                k
                (str_pre i)
                (str_ind j)
                (str_post k)
                S.((pre i && ind j) <= post k)
            else Printf.printf "Empty post: %i\n" k)
          g.post
    in
    List.iter print problems
  ;;

  module Existence = struct
    let bulk_existence_proof formulae =
      List.map BoolExpr.fact_disj formulae
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
          (* Printf.printf "filter: %b\n" r; *)
          r)
        |> Seq.map (fun k -> StepPost (i, j, k))
      in
      let test_queue = ref (Array.to_seq (Array.mapi (fun i _ -> InitPre i) init)) in
      let process q =
        q
        |> Seq.flat_map (function
          | InitPre i ->
            let sat = S.sat (get init i) in
            let _ =
              (* Printf.printf "InitPre\n"; *)
              add_vertex (Init i) sat
            in
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
              (* Printf.printf "PreStep: %b %b\n" sat includes; *)
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
              (* Printf.printf "StepPost: %b %b\n" sat includes; *)
              add_arrow (Step (i, j)) (Post k) includes;
              add_vertex (Post k) sat
            in
            if sat && includes && not (Hashtbl.mem edges (Post k, Pre k))
            then Seq.return (PostPre k)
            else Seq.empty
          | PostPre i ->
            let sat = S.sat (get pre i) in
            let _ =
              (* Printf.printf "PostPre\n"; *)
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

    let solve formulae =
      let proofs = bulk_existence_proof formulae in
      solve_from_parts proofs
    ;;
  end

  module Property = struct
    module OptVarSet = Set.Make (struct
        type t = C.t option

        let compare = Option.compare C.compare
      end)

    module ExprSet = Set.Make (struct
        type t = expr

        let compare = compare
      end)

    let remove_by_var_rule vars = function
      | TagVar (c, _) when OptVarSet.mem (Some c) vars -> None
      | Index _ when OptVarSet.mem None vars -> None
      | _ as e -> Some e
    ;;

    let eliminate_by_clocks vars formula =
      BoolExpr.eliminate (remove_by_var_rule vars) Option.some formula
      |> Option.value ~default:(And [])
    ;;

    let rec flatten_formula = function
      | Or list | And list -> List.flat_map flatten_formula list
      | Linear _ as e -> [ e ]
    ;;

    let remove_by_match_rule constraints f =
      match f with
      | Linear _ ->
        let _, max = ranges_union (clock_index_ranges f) in
        let shifted = BoolExpr.shift_by f (-max) in
        if ExprSet.mem shifted constraints then None else Some f
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

    (** [remove_difference] returns proof obligations without constraints that are in [p] but not in [s]*)
    let remove_difference parts s p =
      if s = []
      then (
        let trivial = Array.make 1 (And []) in
        trivial, trivial, trivial, trivial)
      else if p = []
      then parts
      else (
        let constraint_set formulae =
          formulae
          |> List.to_seq
          |> Seq.flat_map (List.to_seq << BoolExpr.fact_disj)
          |> Seq.flat_map (List.to_seq << enum_specialized)
          |> Seq.flat_map (List.to_seq << flatten_formula << BoolExpr.norm)
          |> ExprSet.of_seq
        in
        let struct_set = constraint_set s in
        let property_set = constraint_set p in
        let diff_constraints = ExprSet.diff property_set struct_set in
        let minus_p_constraints = remove_matching diff_constraints in
        let var_families formulae =
          List.fold_right
            (OptVarSet.add_seq << (List.to_seq << BoolExpr.vars))
            formulae
            OptVarSet.empty
        in
        let struct_families = var_families s in
        let property_families = var_families p in
        let diff_families = OptVarSet.diff property_families struct_families in
        let minus_p_clocks = eliminate_by_clocks diff_families in
        Tuple.map4
          (Array.map (minus_p_clocks << minus_p_constraints << BoolExpr.norm))
          parts)
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

    let solve s p =
      let sp_parts = Existence.bulk_existence_proof (s @ p) in
      let sp_solution = Existence.solve_from_parts sp_parts in
      let s_parts = remove_difference sp_parts s p in
      let s_solution = Existence.solve_from_parts s_parts in
      let simulation_relation = simulate s_solution sp_solution in
      s_solution, sp_solution, simulation_relation
    ;;

    let report (s, sp, sim) = report s, report sp, report sim

    let print_problems (a_sol, ab_sol, sim_sol) =
      let a_problems, ab_problems, sim_problems = report (a_sol, ab_sol, sim_sol) in
      let _ = print_problems a_sol a_problems in
      let _ = print_problems ab_sol ab_problems in
      let print = function
        | NoSolutions -> Printf.printf "No valid simulation at all\n"
        | InitIsLast i ->
          let f, t = Array.get sim_sol.init i in
          Printf.printf
            "------INIT------\n%s\nDOES NOT SIMULATE\n%s\n"
            (S.to_string f)
            (S.to_string t)
        | PreIsLast i ->
          Printf.printf "Precondition %i doesn't have valid simulated steps" i
        | StepIsLast (i, j) ->
          Printf.printf "Step %i %i doesn't lead to valid simulated postconditions" i j
      in
      List.iter print sim_problems
    ;;

    let is_sat results = results |> report |> Tuple.map3 List.is_empty |> Tuple.all3
  end

  module Module = struct

    let solve (a, s, p) =
      let assumption_test = Property.solve a s in
      let property_test = Property.solve (a @ s) p in
      assumption_test, property_test
    ;;

    let is_sat (as_sol, sp_sol) = Property.is_sat as_sol && Property.is_sat sp_sol

    let print_problems (as_sol, sp_sol) =
      Printf.printf "ASSUMPTION PROBLEMS:\n";
      Property.print_problems as_sol;
      Printf.printf "PROPERTY PROBLEMS:\n";
      Property.print_problems sp_sol
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
    let _ = Printf.printf "%s\n" (P.string_of_bool_expr formula) in
    let _ = Format.printf "%s" (D.to_string domain) in
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
