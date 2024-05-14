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

module type Domain = sig
  type t
  type v
  type n

  val top : v -> (v * int) list -> t
  val add_constraint : v -> t -> (v, n) Denotational.bool_expr -> t
  val leq : t -> t -> bool
  val is_bottom : t -> bool
  val is_top : t -> bool
  val meet : t -> t -> t
  val diff : t -> t -> t list
  val more_precise : t -> t -> bool
  val infinite_in : v -> t -> bool

  include Interface.Stringable with type t := t
end

module Make (C : Var) (N : Num) = struct
  open Denotational
  open Rtccsl
  open MakeDebug (C) (N)

  module N = struct
    include N
    include Interface.ExpOrder.Make (N)
  end

  module NumExpr = MakeExtNumExpr (N)

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

  let exact_spec (s : ('c, 'n) specification) : ('c, 'n) bool_expr =
    And (List.map exact_rel s)
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

  let safe_over_rel c =
    try over_rel c with
    | ExactRelationUnavailable | OverApproximationUnavailable -> And []
  ;;

  (** Returns underapproximation denotational relation of a RTCCSL constraint. Raises [UnderApproximationUnavailable] if doesn't exist.*)
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

  let lc_connection c i = Denotational.Syntax.((c @ Stdlib.(i - 1)) < c @ i)

  module SetCI = Set.Make (struct
      type t = C.t * int

      let compare (c1, i1) (c2, i2) =
        let comp = C.compare c1 c2 in
        if comp = 0 then Int.compare i1 i2 else comp
      ;;
    end)

  let vars formula =
    List.sort_uniq (Tuple.compare2 C.compare Int.compare) (BoolExpr.vars_except_i formula)
  ;;

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

      let compare x y =
        match x, y with
        | None, None -> 0
        | Some _, None -> -1
        | None, Some _ -> 1
        | Some x, Some y -> C.compare x y
      ;;
    end)

  let clock_index_ranges formula =
    let rule c i acc =
      let l, r = MapOCMM.find_opt c acc |> Option.value ~default:(0, 0) in
      MapOCMM.add c Int.(min i l, max i r) acc
    in
    BoolExpr.fold rule MapOCMM.empty formula
  ;;

  let ranges_union r =
    let reduce _ (lmin, lmax) (gmin, gmax) = Int.min lmin gmin, Int.max lmax gmax in
    MapOCMM.fold reduce r (0, 0)
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

  (** The rule to unpack zerocond expressions.
      i > index -> use indexed expression
      i = index -> use initial condition
      i < index -> remove*)
  let reduce_zerocond index = function
    | ZeroCond (Index i, _) when i > index -> Some (Index i)
    | ZeroCond (Index i, init) when i = index -> Some (Const init)
    | ZeroCond ((TagVar (_, i) as v), _) when i > index -> Some v
    | ZeroCond (TagVar (_, i), init) when i = index -> Some (Const init)
    | ZeroCond _ -> None
    | _ as e -> Some e
  ;;

  (** The rule to remove all expressions that reference non-existent past in initial condition: i < index.*)
  let reduce_negative index = function
    | (Index i | TagVar (_, i)) when i <= index -> None
    | _ as e -> Some e
  ;;

  (** Returns basic condition for a logical clock: [0 < c[1]]*)
  let lc_init c = Denotational.Syntax.(Const N.zero < c @ 1)

  (** Returns initial condition for the [formulae] of the given [width].*)
  let init_cond width formulae =
    let norm_reduce_nonzero index f =
      let f = NumExpr.norm_rule f in
      let* f = reduce_zerocond index f in
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
      elimination_of_texp_only (reduce_negative index_to_reduce)
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
    let _ = Printf.printf "init: %s\n" (string_of_bool_expr init) in
    let _ = Printf.printf "pre: %s\n" (string_of_bool_expr pre) in
    let _ = Printf.printf "step: %s\n" (string_of_bool_expr cond) in
    let _ = Printf.printf "post: %s\n" (string_of_bool_expr post) in
    init, pre, cond, post
  ;;

  module Solver = struct
    module type S = sig
      type t
      type v
      type f = (C.t, N.t) bool_expr

      val of_formula : f -> t
      val sat : t -> bool
      val ( <= ) : t -> t -> bool
      val ( && ) : t -> t -> t
      val diff : t -> t -> t list
      val more_precise : t -> t -> bool
      val index_name : v
      val infinite_in : v -> t -> bool

      include Interface.Stringable with type t := t
    end

    module type D = sig
      include Domain with type v = C.t and type n = N.t

      val index_name : v
    end

    module MakeFromDomain (D : D) = struct
      include D

      type f = (C.t, N.t) bool_expr

      let of_formula f = add_constraint D.index_name (D.top D.index_name (vars f)) f
      let sat = not << is_bottom
      let ( && ) = meet
      let ( <= ) = leq
    end
  end

  module ExistenceProof (S : Solver.S) = struct
    type 'a vertix =
      | Init of 'a
      | Pre of 'a
      | Step of 'a * 'a
      | Post of 'a
    [@@deriving sexp]

    type ('f, 's) t =
      { init : 'f array
      ; pre : 'f array
      ; ind : 'f array
      ; post : 'f array
      ; arrows : (int vertix * int vertix, 's) Hashtbl.t
      ; vertices : (int vertix, 's) Hashtbl.t
      }

    type test =
      | InitPre of int
      | PreStep of int * int
      | StepPost of int * int * int
      | PostPre of int

    let solve formulae =
      let init, pre, ind, post =
        List.map BoolExpr.fact_disj formulae
        |> List.general_cartesian
        |> List.map existence_proof
        |> List.split4
        |> Tuple.map4 Array.of_list
      in
      let len = Array.length init in
      let vertices = Hashtbl.create ((len * len) + (3 * len)) in
      let add_vertex v r = Hashtbl.replace vertices v r in
      let arrows = Hashtbl.create (2 * ((len * len) + (3 * len))) in
      let add_arrow from into r = Hashtbl.replace arrows (from, into) r in
      let init, pre, ind, post =
        Tuple.map4 (Array.map S.of_formula) (init, pre, ind, post)
      in
      let steps_by_pre i =
        Seq.int_seq (Array.length ind)
        |> Seq.filter (fun j -> not (Hashtbl.mem arrows (Pre i, Step (i, j))))
        |> Seq.map (fun j -> PreStep (i, j))
      in
      let post_inclusions_by_step (i, j) =
        Seq.int_seq (Array.length post)
        |> Seq.filter (fun k ->
          let r = not (Hashtbl.mem arrows (Step (i, j), Post k)) in
          (* Printf.printf "filter: %b\n" r; *)
          r)
        |> Seq.map (fun k -> StepPost (i, j, k))
      in
      let test_queue = ref (Array.to_seq (Array.mapi (fun i _ -> InitPre i) init)) in
      let process q =
        q
        |> Seq.flat_map (function
          | InitPre i ->
            let sat = S.sat (Array.get init i) in
            let _ =
              (* Printf.printf "InitPre\n"; *)
              add_vertex (Init i) sat
            in
            if sat
            then (
              let sat = S.sat (Array.get pre i) in
              let _ = add_vertex (Pre i) sat in
              if sat
              then (
                add_arrow (Init i) (Pre i) sat;
                steps_by_pre i)
              else Seq.empty)
            else Seq.empty
          | PreStep (p, i) ->
            let pre = Array.get pre p in
            let ind = Array.get ind i in
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
            let pre = Array.get pre i in
            let ind = Array.get ind j in
            let post = Array.get post k in
            let step = S.(pre && ind) in
            let sat = S.sat post in
            let includes = S.(step <= post) in
            let _ =
              (* Printf.printf "StepPost: %b %b\n" sat includes; *)
              add_arrow (Step (i, j)) (Post k) includes;
              add_vertex (Post k) sat
            in
            if sat && includes && not (Hashtbl.mem arrows (Post k, Pre k))
            then Seq.return (PostPre k)
            else Seq.empty
          | PostPre i ->
            let sat = S.sat (Array.get pre i) in
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
      { init; pre; ind; post; arrows; vertices }
    ;;

    type problem =
      | NoSolutions
      | InitIsLast of int
      | PreIsLast of int
      | StepIsLast of int * int

    let vertix_to_string v =
      v |> sexp_of_vertix Sexplib0.Sexp_conv.sexp_of_int |> Sexplib0.Sexp.to_string
    ;;

    let report { init; vertices; arrows; _ } =
      (* let _ =
         Hashtbl.iter
         (fun v sat -> Printf.printf "%s: %b\n" (vertix_to_string v) sat)
         vertices
         in
         let _ =
         Hashtbl.iter
         (fun (f, t) sat ->
         Printf.printf "%s -> %s: %b\n" (vertix_to_string f) (vertix_to_string t) sat)
         arrows
         in *)
      let len = Array.length init in
      let in_cycle = Hashtbl.create ((len * len) + (2 * len)) in
      let mark_cyclic v = Hashtbl.replace in_cycle v true in
      let visited = Hashtbl.create ((len * len) + (2 * len)) in
      let is_cyclic v = Hashtbl.value in_cycle v false || Hashtbl.mem visited v in
      let visit v = Hashtbl.replace visited v () in
      let next =
        arrows
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
        |> List.mapi (fun i dom -> if S.sat dom then dfs (Init i) else false, [])
        |> List.split
      in
      let problems = List.concat problems in
      if not (List.any valid_starts) then NoSolutions :: problems else problems
    ;;

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
                  "Non-empty unreachable post: %i %i % i\n\
                   pre:\n\
                   %s\n\
                   ind:\n\
                   %s\n\
                   post:\n\
                   %s\n\
                   %b"
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
  end
  (*
     module PropertyProof (S : Solver.S) = struct
     module E = ExistenceProof (S)

     type ('f, 's) t = ('f, 's) E.t * ('f, 's) E.t * (int E.vertix, 's) Hashtbl.t

     let solve base prop = ()
     let unsolved (base, prop, relations) = ()
     let print_problems problems = ()
     end *)
end

module type Alloc = sig
  type dom

  val alloc : dom Apron.Manager.t
end

exception NonConvex

module PolkaDomain
    (A : Alloc)
    (V : Var)
    (N : sig
       type t

       val to_rational : t -> Number.Rational.t
     end) =
struct
  open Denotational
  open Apron

  type t = A.dom Abstract1.t
  type n = N.t
  type v = V.t

  let pp_var (v, i) = Printf.sprintf "%s[%i]" (V.to_string v) i
  let v_to_var = Var.of_string << V.to_string

  let top index reals =
    let index_var = v_to_var index in
    let reals = Array.of_seq (Seq.map (Var.of_string << pp_var) (List.to_seq reals)) in
    Abstract1.top A.alloc (Environment.make [| index_var |] reals)
  ;;

  let rec add_constraint index domain =
    let env = Abstract1.env domain in
    let index_var = v_to_var index in
    let op2op = function
      | Add -> Texpr1.Add
      | Sub -> Texpr1.Sub
      | Mul -> Texpr1.Mul
      | Div -> Texpr1.Div
    in
    let rec te2te = function
      | TagVar (v, i) ->
        let var = Var.of_string (pp_var (v, i)) in
        Texpr1.var env var
      | Index i ->
        Texpr1.binop
          Texpr1.Add
          (Texpr1.var env index_var)
          (Texpr1.cst env (Coeff.s_of_int i))
          Texpr1.Int
          Texpr1.Near
      | Const c -> Texpr1.cst env (Coeff.s_of_mpqf @@ N.to_rational c)
      | Op (l, op, r) -> Texpr1.binop (op2op op) (te2te l) (te2te r) Texpr1.Real Near
      | ZeroCond _ | Min _ | Max _ -> raise NonConvex
    in
    function
    | And [] -> domain
    | And list -> List.fold_left (add_constraint index) domain list
    | Or _ -> invalid_arg "polyhedra only supports conjunctions"
    | Linear (l, op, r) ->
      let diff = Texpr1.binop Texpr1.Sub (te2te l) (te2te r) Texpr1.Real Texpr1.Near in
      let op, expr =
        match op with
        | Eq -> Tcons1.EQ, diff
        | Less -> Tcons1.SUP, Texpr1.unop Texpr1.Neg diff Texpr1.Real Texpr1.Near
        | LessEq -> Tcons1.SUPEQ, Texpr1.unop Texpr1.Neg diff Texpr1.Real Texpr1.Near
        | More -> Tcons1.SUP, diff
        | MoreEq -> Tcons1.SUPEQ, diff
      in
      let lincond = Tcons1.make expr op in
      let _ = Format.printf "%a\n" Tcons1.print lincond in
      let array = Tcons1.array_make env 1 in
      let _ = Tcons1.array_set array 0 lincond in
      Abstract1.meet_tcons_array A.alloc domain array
  ;;

  let leq = Apron.Abstract1.is_leq A.alloc
  let is_bottom = Apron.Abstract1.is_bottom A.alloc
  let is_top = Apron.Abstract1.is_top A.alloc
  let to_string d = Format.asprintf "%a" Abstract1.print d
  let meet = Apron.Abstract1.meet A.alloc
  let diff _ _ = failwith "not implemented"
  let more_precise _ _ = failwith "not implemented"
  let infinite_in _ _ = failwith "not implemented"
end

module VPLDomain
    (V : Var)
    (N : sig
       type t

       val to_rational : t -> Number.Rational.t
     end) =
struct
  open Denotational
  module Ident = Vpl.UserInterface.Lift_Ident (String)

  module Term = struct
    type t = Vpl.WrapperTraductors.Interface(Vpl.Domains.UncertifiedQ.Coeff).Term.t

    let to_term t = t
    let of_term t = t
  end

  module D = Vpl.UserInterface.MakeCustom (Vpl.Domains.UncertifiedQ) (Ident) (Term)
  module VarSet = Set.Make (String)

  type aux =
    { b_expr : D.b_expr list
    ; vars : VarSet.t
    }

  let aux_union x y = { b_expr = x.b_expr @ y.b_expr; vars = VarSet.union x.vars y.vars }
  let aux_empty = { b_expr = []; vars = VarSet.empty }

  type t = aux * D.t
  type v = V.t
  type n = N.t

  let to_q x =
    let x = N.to_rational x in
    let num = Mpz.get_int (Mpqf.get_num x) in
    let den = Mpz.get_int (Mpqf.get_den x) in
    Q.make (Z.of_int num) (Z.of_int den)
  ;;

  let var_str (v, i) = Printf.sprintf "%s[%i]" (V.to_string v) i
  let var (v, i) = Ident.toVar (var_str (v, i))
  let index_var index = Ident.toVar @@ V.to_string index
  let top _ _ = aux_empty, D.top
  let leq (_, x) (_, y) = D.leq x y
  let meet (auxx, x) (auxy, y) = aux_union auxx auxy, D.meet x y

  (*FIXME: need more tests to check if it actually works in all cases*)
  let is_top (_, d) = d = D.top
  let is_bottom (_, x) = D.is_bottom x
  let to_string (_, x) = D.to_string V.to_string x

  let rec te2ae index = function
    | TagVar (v, i) -> D.Term.Var (var (v, i))
    | Const n -> D.Term.Cte (to_q n)
    | Index i -> D.Term.Add (D.Term.Var (index_var index), D.Term.Cte (Q.of_int i))
    | Op (l, op, r) ->
      let l = te2ae index l in
      let r = te2ae index r in
      (match op with
       | Add -> D.Term.Add (l, r)
       | Sub -> D.Term.Add (l, D.Term.Opp r)
       | Mul -> D.Term.Mul (l, r)
       | Div -> D.Term.Div (l, r))
    | ZeroCond _ | Min _ | Max _ -> raise NonConvex
  ;;

  let op2op = function
    | Eq -> Vpl.Cstr_type.EQ
    | More -> Vpl.Cstr_type.GT
    | Less -> Vpl.Cstr_type.LT
    | MoreEq -> Vpl.Cstr_type.GE
    | LessEq -> Vpl.Cstr_type.LE
  ;;

  let rec add_constraint index (aux, domain) = function
    | And [] -> aux, domain
    | And list -> List.fold_left (add_constraint index) (aux, domain) list
    | Or _ -> invalid_arg "polyhedra only supports conjunctions"
    | Linear (l, op, r) as e ->
      let lincond = D.Cond.Atom (te2ae index l, op2op op, te2ae index r) in
      let bexp = D.of_cond lincond in
      let vars =
        e
        |> BoolExpr.indexed_vars
        |> List.map (function
          | Some v, i -> var_str (v, i)
          | None, _ -> V.to_string index)
        |> VarSet.of_list
      in
      aux_union aux { b_expr = [ bexp ]; vars }, D.assume bexp domain
  ;;

  let diff (_, x) (_, y) = List.map (fun x -> aux_empty, x) (D.diff x y)

  (** Checks that b is strictly more precise than a.*)
  let more_precise (aa, a) (ab, b) =
    (* let _ = List.iter (fun v -> Printf.printf "%s " v) (VarSet.elements aa.vars) in *)
    let diffvars = VarSet.elements @@ VarSet.diff ab.vars aa.vars in
    D.leq a (D.project diffvars b)
  ;;

  let infinite_in var (_, dom) =
    let var = D.Term.Var (Ident.toVar @@ V.to_string var) in
    D.get_upper_bound var dom
    |> Option.map (function
      | Vpl.Pol.Infty -> true
      | _ -> false)
    |> Option.value ~default:false
  ;;
end

module MakeWithPolyhedra
    (V : Var)
    (N : Num)
    (D : Domain with type v = V.t and type n = N.t) =
struct
  include Make (V) (N)

  let to_polyhedra index_name formula =
    let formula = Denotational.BoolExpr.norm formula in
    D.add_constraint index_name (D.top index_name (vars formula)) formula
  ;;

  type report = unit

  (* let analyze index_name spec assertion : report = () *)
end

module Test
    (MakeDomain : functor
       (V : Var)
       (N : sig
          type t

          val to_rational : t -> Number.Rational.t
        end)
       -> Domain with type v = V.t and type n = N.t) =
struct
  module N = struct
    include Number.Rational

    let to_rational = Fun.id
  end

  module D = MakeDomain (String) (N)

  module P = struct
    include Denotational.MakeDebug (String) (N)
    include MakeWithPolyhedra (String) (N) (D)
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
    include Test (PolkaDomain (struct
        type dom = Polka.loose Polka.t

        let alloc = Polka.manager_alloc_loose ()
      end))
  end)
;;

let%test_module _ =
  (module struct
    include Test (VPLDomain)
  end)
;;
