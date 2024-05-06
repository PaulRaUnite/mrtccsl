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

  exception NoExactConvexRelation

  let exact_rel c =
    let open Syntax in
    let i = 0 in
    (*dummy variable*)
    match c with
    | Precedence { cause; effect } -> cause @ i < effect @ i
    | Causality { cause; effect } -> cause @ i <= effect @ i
    | RTdelay { out; arg; delay = e1, e2 } -> (out @ i) - (arg @ i) |> (Const e1, Const e2)
    | Delay { out; arg; delay = d1, d2; base = None } when Stdlib.(d1 = d2) ->
      (out @ Stdlib.(i - d1)) = arg @ i
    | Fastest { out; left; right } -> out @ i = min (left @ i) (right @ i)
    | Slowest { out; left; right } -> out @ i = max (left @ i) (right @ i)
    | CumulPeriodic { out; period; error = le, re; offset } ->
      let prev = ZeroCond ((out @ Stdlib.(i - 1)), offset) in
      (out @ i) - prev |> N.(Const (period + le), Const (period + re))
    | AbsPeriodic { out; period; error = le, re; offset } ->
      (out @ i) - (Const period * Index Stdlib.(i - 1)) - Const offset
      |> (Const le, Const re)
    | Sporadic { out; at_least; strict } ->
      let diff = (out @ i) - ZeroCond ((out @ Stdlib.(i - 1)), N.zero) in
      if strict then diff > Const at_least else diff >= Const at_least
    | _ -> raise NoExactConvexRelation
  ;;

  let exact_spec (s : ('c, 'n) specification) : ('c, 'n) bool_expr =
    And (List.map exact_rel s)
  ;;

  exception NoOverApproximation

  let over_rel c =
    try exact_rel c with
    | NoExactConvexRelation ->
      let open Syntax in
      let i = 0 in
      (match c with
       | FirstSampled { out; arg; base } | LastSampled { out; arg; base } ->
         let _ = arg in
         (base @ Stdlib.(i - 1)) < out @ i && out @ i <= base @ i
       | _ -> raise NoOverApproximation)
  ;;

  let safe_over_rel c =
    try over_rel c with
    | NoExactConvexRelation | NoOverApproximation -> And []
  ;;

  exception NoUnderApproximation

  let under_rel c =
    try exact_rel c with
    | NoExactConvexRelation ->
      let open Syntax in
      let i = 0 in
      (match c with
       | FirstSampled { out; arg; base } | LastSampled { out; arg; base } ->
         let _ = arg in
         (base @ Stdlib.(i - 1)) < out @ i && out @ i = arg @ i && arg @ i <= base @ i
       | Sample { out; arg; base } ->
         out @ i = base @ i
         && arg @ i |> (ZeroCond ((base @ Stdlib.(i - 1)), N.zero), base @ i)
       | _ -> raise NoUnderApproximation)
  ;;

  let lc_init c = Denotational.Syntax.(Const N.zero < c @ 0)
  let lc_connection c i = Denotational.Syntax.((c @ Stdlib.(i - 1)) < c @ i)

  module SetCI = Set.Make (struct
      type t = C.t * int

      let compare (c1, i1) (c2, i2) =
        let comp = C.compare c1 c2 in
        if comp = 0 then Int.compare i1 i2 else comp
      ;;
    end)

  let vars_set formula =
    let vars =
      fold_bexp
        (fun x i set ->
          match x with
          | Some v -> SetCI.add (v, i) set
          | None -> set)
        SetCI.empty
        formula
    in
    vars
  ;;

  let vars formula = SetCI.elements (vars_set formula)

  let vars_of_list formulae =
    SetCI.elements
    @@ List.fold_left (fun acc f -> SetCI.union acc (vars_set f)) SetCI.empty formulae
  ;;

  let inductive_step formulae =
    use_more_cond_bexp
    @@ And (formulae @ List.map (fun (c, i) -> lc_connection c i) (vars_of_list formulae))
  ;;

  let clocks_of_list formulae =
    let module SetC = Set.Make (C) in
    let fold_formula =
      fold_bexp (fun c _ acc ->
        match c with
        | Some c -> SetC.add c acc
        | None -> acc)
    in
    let clocks_set = List.fold_left fold_formula SetC.empty formulae in
    SetC.elements clocks_set
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

  let index_ranges formula =
    let rule c i acc =
      let l, r = MapOCMM.find_opt c acc |> Option.value ~default:(0, 0) in
      MapOCMM.add c Int.(min i l, max i r) acc
    in
    fold_bexp rule MapOCMM.empty formula
  ;;

  let combine_index_ranges l =
    let combine_records _ (min1, max1) (min2, max2) =
      Some Int.(min min1 min2, max max1 max2)
    in
    List.fold_left
      (fun acc lacc -> MapOCMM.union combine_records acc lacc)
      MapOCMM.empty
      l
  ;;

  let range_to_min_max r =
    let reduce k (l, r) = function
      | None -> Some ((k, l), (k, r))
      | Some ((lc, gmin), (rc, gmax)) ->
        let nmin = Int.min l gmin in
        let nmax = Int.max r gmax in
        let nlc = if nmin < gmin then k else lc in
        let nrc = if nmax > gmax then k else rc in
        Some ((nlc, nmin), (nrc, nmax))
    in
    let (lc, min), (rc, max) = Option.get @@ MapOCMM.fold reduce r None in
    (* let _ = Printf.printf "%s,%i,%s,%i\n" (Option.map C.to_string lc |> Option.value ~default:"") min (Option.map C.to_string rc |> Option.value ~default:"") max in *)
    if lc = rc then min + 1, max else min, max
  ;;

  let postcondition formulae =
    let clocks = clocks_of_list formulae in
    let ranges = List.map index_ranges formulae in
    let intervals = List.map range_to_min_max ranges in
    let min, max = range_to_min_max (combine_index_ranges ranges) in
    let neg_ints = List.init (Int.neg min + 1) Int.neg in
    let clock_connections =
      List.map (fun (c, i) -> lc_connection c i) (List.cartesian clocks neg_ints)
    in
    let _ = assert (max = 0) in
    let expand f min =
      let neg_ints = List.init (Int.neg min + 1) Int.neg in
      List.map (fun i -> map_ind_bexp (fun _ j -> i + j) f) neg_ints
    in
    let expanded_formulae =
      List.flatten
      @@ List.map (fun (f, (lmin, _)) -> expand f (min - lmin))
      @@ List.combine formulae intervals
    in
    And (expanded_formulae @ clock_connections)
  ;;

  let precondition post = map_ind_bexp (fun _ i -> i - 1) post

  (*TODO: move to proper module*)
  let norm_texp_rule expr =
    match expr with
    | Op (Const n, op, Const n') ->
      Const
        (match op with
         | Add -> N.(n + n')
         | Sub -> N.(n - n')
         | Mul -> N.(n * n')
         | Div -> N.(n / n'))
    | Op (Const n, Add, e) | Op (e, Add, Const n) -> if N.equal n N.zero then e else expr
    | Min (Const l, Const r) -> Const (N.min l r)
    | Max (Const l, Const r) -> Const (N.max l r)
    | ZeroCond (Const n, init) -> Const (N.max n init)
    | _ -> expr
  ;;

  let reduce_by_idx index expr =
    match expr with
    | (TagVar (_, i) | Index i) when i = index -> Const N.zero
    | Index i -> Index i
    | ZeroCond (Index i, _) when i > index -> Index i
    | ZeroCond ((TagVar (_, i) as v), _) when i > index -> v
    | ZeroCond _ -> failwith "zerocond should be simplified by this point"
    | _ -> expr
  ;;

  let init_cond post =
    let _ = Printf.printf "init: %s\n" (string_of_bool_expr post) in
    let assume_init = texp_reduce (norm_texp_rule << reduce_by_idx 0 << norm_texp_rule) in
    let init_cond_bexp = bexp_reduce assume_init Fun.id in
    let min, max = fold_bexp (fun _ i (l, r) -> Int.(min i l, max i r)) (0, 0) post in
    let _ = Printf.printf "%i, %i\n" min max in
    let _ = assert (max = 0) in
    let post = post |> map_ind_bexp (fun _ i -> i - min) in
    let _ = Printf.printf "init: %s\n" (string_of_bool_expr post) in
    let post = post |> init_cond_bexp |> norm in
    let _ = assert (not @@ empty_bexp post) in
    post
  ;;

  let existence_proof formulae =
    let post_compound = postcondition formulae in
    let _ = Printf.printf "post_comp: %s\n" (string_of_bool_expr post_compound) in
    let post = use_more_cond_bexp post_compound in
    let cond = inductive_step formulae in
    let pre = precondition post in
    let init = init_cond post_compound in
    Tuple.map4 norm (init, pre, cond, post)
  ;;

  module Solver = struct
    module type S = sig
      type t
      type f = (C.t, N.t) bool_expr

      val of_formula : f -> t
      val sat : t -> bool
      val ( <= ) : t -> t -> bool
      val ( && ) : t -> t -> t

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
    type ('f, 's) t =
      { init : ('f * 's) array
      ; pre : 'f array
      ; ind : 'f array
      ; post : 'f array
      ; steps : (int * int, 's) Hashtbl.t
      ; inclusion : (int * int * int, 's) Hashtbl.t
      }

    let solve formulae =
      let init, pre, ind, post =
        List.map fact_disj_bexp formulae
        |> List.general_cartesian
        |> List.map existence_proof
        |> List.split4
        |> Tuple.map4 Array.of_list
      in
      let len = Array.length init in
      let steps = Hashtbl.create (len * len) in
      let inclusion = Hashtbl.create (len * len * len) in
      let init =
        Array.map
          (fun f ->
            let dom = S.of_formula f in
            dom, S.sat dom)
          init
      in
      let pre, ind, post = Tuple.map3 (Array.map S.of_formula) (pre, ind, post) in
      let steps_by_pre i = Seq.int_seq (Array.length ind) |> Seq.map (fun j -> i, j) in
      let inclusions_by_step (i, j) =
        Seq.int_seq (Array.length post) |> Seq.map (fun k -> i, j, k)
      in
      let reachable_steps =
        ref
          (init
           |> Array.to_seqi
           |> Seq.filter (fun (_, (_, sat)) -> sat)
           |> Seq.flat_map (fun (i, _) -> steps_by_pre i))
      in
      let reachable_inclusions = ref Seq.empty in
      let process_steps q =
        q
        |> Seq.filter (fun (p, i) ->
          let result = S.sat S.(Array.get pre p && Array.get ind i) in
          let _ = Hashtbl.replace steps (p, i) result in
          result)
        |> Seq.flat_map (fun (p, i) -> inclusions_by_step (p, i))
        |> Seq.filter (fun key -> not (Hashtbl.value inclusion key false))
      in
      let process_inclusions q =
        q
        |> Seq.filter (fun (pr, i, po) ->
          let result = S.((Array.get pre pr && Array.get ind i) <= Array.get post po) in
          let _ = Hashtbl.replace inclusion (pr, i, po) result in
          result)
        |> Seq.flat_map (fun (_, _, po) -> steps_by_pre po)
        |> Seq.filter (fun key -> not (Hashtbl.value steps key false))
      in
      let _ =
        while not (Seq.is_empty !reachable_steps && Seq.is_empty !reachable_inclusions) do
          reachable_inclusions := process_steps !reachable_steps;
          reachable_steps := process_inclusions !reachable_inclusions
        done
      in
      { init; pre; ind; post; steps; inclusion }
    ;;

    type 'a vertix =
      | Pre of 'a
      | Step of 'a * 'a
      | Post of 'a

    let unsolved { init; steps; inclusion; _ } =
      (* let _ = Array.iteri (fun i (_, sat) -> Printf.printf "%i:%b\n" i sat) init in
         let _ = Hashtbl.iter (fun (i, j) v -> Printf.printf "%i,%i,%b\n" i j v) steps in
         let _ =
         Hashtbl.iter (fun (i, j, k) v -> Printf.printf "%i,%i,%i,%b\n" i j k v) inclusion
         in *)
      let len = Array.length init in
      let marks = Hashtbl.create ((len * len) + (2 * len)) in
      let add_vertex v = Hashtbl.replace marks v false in
      (* let print_marks m =
         Hashtbl.iter
         (fun k v ->
         match k with
         | Pre i -> Printf.printf "pre %i: %b\n" i v
         | Step (i, j) -> Printf.printf "step %i %i: %b\n" i j v
         | Post i -> Printf.printf "post %i: %b\n" i v)
         m
         in *)
      let visited = Hashtbl.create ((len * len) + (2 * len)) in
      let next = Hashtbl.create (Hashtbl.length steps + Hashtbl.length inclusion) in
      let add_arrow v v' = Hashtbl.entry next (List.cons v') v [] in
      let _ =
        for i = 0 to len - 1 do
          add_vertex (Pre i);
          add_vertex (Post i);
          add_arrow (Post i) (Pre i);
          for j = 0 to len - 1 do
            if Hashtbl.find_opt steps (i, j) |> Option.value ~default:false
            then (
              add_vertex (Step (i, j));
              add_arrow (Pre i) (Step (i, j)));
            if Hashtbl.find_opt inclusion (i, j, j) |> Option.value ~default:false
            then add_arrow (Step (i, j)) (Post j)
          done
        done
      in
      (* let _ = print_marks marks in *)
      let roots =
        init
        |> Array.to_seqi
        |> Seq.filter_map (fun (i, (_, sat)) -> if sat then Some (Pre i) else None)
      in
      let rec dfs v =
        if Hashtbl.find marks v || Hashtbl.mem visited v
        then (
          let _ = Hashtbl.replace visited v () in
          let _ = Hashtbl.replace marks v true in
          true)
        else (
          let _ = Hashtbl.replace visited v () in
          if List.any (List.map dfs (Hashtbl.value next v []))
          then (
            let _ = Hashtbl.replace marks v true in
            true)
          else false)
      in
      let _ = Seq.iter (ignore << dfs) roots in
      (* let _ = Printf.printf "after\n"in
         let _ = print_marks marks in *)
      Hashtbl.to_seq marks
      |> Seq.filter_map (fun (v, sat) -> if sat then None else Some v)
      |> List.of_seq
    ;;

    let print_problems g l =
      let print = function
        | Pre i ->
          let d = Array.get g.pre i in
          Printf.printf "=== Precondition %i : NO SAT STEPS ===\n%s\n" i (S.to_string d)
        | Step (i, j) ->
          let d1 = Array.get g.pre i in
          let d2 = Array.get g.ind j in
          let d3 = Array.get g.post j in
          Printf.printf
            "=== Pre %i, Ind %i ===\n%s\n+++AND+++\n%s\n+++NOT INCLUDED+++\n%s\n\n"
            i
            j
            (S.to_string d1)
            (S.to_string d2)
            (S.to_string d3)
        | Post i ->
          let d = Array.get g.post i in
          Printf.printf "=== Postcondition %i : UNREACHABLE ===\n%s\n" i (S.to_string d)
      in
      List.iter print l
    ;;
    (*
       let leq g g' =
    *)
  end
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

  type t = Vpl.UserInterface.UncertifiedQ.t
  type v = V.t
  type n = N.t

  let to_q x =
    let x = N.to_rational x in
    let num = Mpz.get_int (Mpqf.get_num x) in
    let den = Mpz.get_int (Mpqf.get_den x) in
    Q.make (Z.of_int num) (Z.of_int den)
  ;;

  let var (v, i) = Ident.toVar @@ Printf.sprintf "%s[%i]" (V.to_string v) i
  let top _ _ = D.top
  let leq = D.leq
  let meet = D.meet

  (*FIXME: need more tests to check if it actually works in all cases*)
  let is_top d = d = D.top
  let is_bottom = D.is_bottom
  let to_string = D.to_string V.to_string

  let rec te2ae index = function
    | TagVar (v, i) -> D.Term.Var (var (v, i))
    | Const n -> D.Term.Cte (to_q n)
    | Index i ->
      D.Term.Add (D.Term.Var (Ident.toVar @@ V.to_string index), D.Term.Cte (Q.of_int i))
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

  let rec add_constraint index domain = function
    | And [] -> domain
    | And list -> List.fold_left (add_constraint index) domain list
    | Or _ -> invalid_arg "polyhedra only supports conjunctions"
    | Linear (l, op, r) ->
      let lincond = D.Cond.Atom (te2ae index l, op2op op, te2ae index r) in
      D.assume (D.of_cond lincond) domain
  ;;
end

module MakeWithPolyhedra
    (V : Var)
    (N : Num)
    (D : Domain with type v = V.t and type n = N.t) =
struct
  include Make (V) (N)

  let to_polyhedra index_name formula =
    let formula = Denotational.norm formula in
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
