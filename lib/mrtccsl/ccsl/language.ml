open Prelude
open Expr

type 'a interval = 'a * 'a [@@deriving map, show, fold]

type ('v, 'n) param =
  | Var of 'v
  | Const of 'n
[@@deriving map, show, fold]

let var v = Var v
let const c = Const c

(**RTCCSL constraint type. ['c] is clock variable type, ['p] is parameter variable type, ['n] numerical constraint type. *)
type ('c, 'tp, 'ip, 'tv, 'iv, 't) constr =
  | Precedence of
      { cause : 'c
      ; conseq : 'c
      }
  | Causality of
      { cause : 'c
      ; conseq : 'c
      }
  | Exclusion of 'c list * 'iv option
  | Coincidence of 'c list
  | Subclocking of
      { sub : 'c
      ; super : 'c
      ; dist : 'iv option
      }
  | Minus of
      { out : 'c
      ; arg : 'c
      ; except : 'c list
      }
  | Delay of
      { out : 'c
      ; arg : 'c
      ; delay : ('iv, int) param
      ; base : 'c option
      }
  | Fastest of
      { out : 'c
      ; args : 'c list
      }
  | Slowest of
      { out : 'c
      ; args : 'c list
      }
  | Intersection of
      { out : 'c
      ; args : 'c list
      }
  | Union of
      { out : 'c
      ; args : 'c list
      }
  | Periodic of
      { out : 'c
      ; base : 'c
      ; period : ('iv, int) param
      ; skip : ('iv, int) param option
      }
  | Sample of
      { out : 'c
      ; arg : 'c
      ; base : 'c
      }
  | Alternate of
      { first : 'c
      ; second : 'c
      }
  | RTdelay of
      { out : 'c
      ; arg : 'c
      ; delay : ('tv, 't) param
      }
  (* | Offset of
      { out : 'c
      ; delay : 'p
      } *)
  | CumulPeriodic of
      { out : 'c
      ; period : 't
      ; error : ('tv, 't) param
      ; offset : ('tp, 't) param
      }
  | AbsPeriodic of
      { out : 'c
      ; period : 't
      ; error : ('tv, 't) param
      ; offset : ('tp, 't) param
      }
  | FirstSampled of
      { out : 'c
      ; arg : 'c
      ; base : 'c
      }
  | LastSampled of
      { out : 'c
      ; arg : 'c
      ; base : 'c
      }
  | Forbid of
      { from : 'c
      ; until : 'c
      ; args : 'c list
      }
  | Allow of
      { from : 'c
      ; until : 'c
      ; args : 'c list
      }
  | Sporadic of
      { out : 'c
      ; at_least : ('tp, 't) param
      ; strict : bool
      } (**Mutex is a special case of Pool where [n=1]*)
  | Pool of int * ('c * 'c) list
  | DisjunctiveUnion of
      { out : 'c
      ; args : 'c list
      ; ratios : 'iv option
      }
[@@deriving map, show, fold]

(*TODO: replace rt.constraints with just delay and offset. *)
(* module Complex = struct
  let cumul_periodic out period_var offset_par = [ RTdelay { out; arg = out } ]
end *)

type ('v, 'n) numeric_rel_constr = NumRelation of 'v * num_rel * ('v, 'n) param
[@@deriving map, show, fold]

(**Type of distributions that can be used in a simulation. *)
type 'n distribution =
  | Uniform
  | Normal of
      { mean : 'n
      ; deviation : 'n
      }
  | Exponential of 'n
[@@deriving map, show, fold]

type ('iv, 'tv, 't) probability_constr =
  | DiscreteProcess of
      { name : 'iv
      ; ratios : (int * int) list
      }
  | ContinuousProcess of
      { name : 'tv
      ; dist : 't distribution
      }
[@@deriving map, show, fold]

let name = function
  | Precedence _ -> "precedence"
  | Causality _ -> "causality"
  | Exclusion _ -> "exclusion"
  | Coincidence _ -> "coincidence"
  | Subclocking _ -> "subclocking"
  | Minus _ -> "minus"
  | Delay _ -> "delay"
  | Fastest _ -> "fastest"
  | Slowest _ -> "slowest"
  | Intersection _ -> "intersection"
  | Union _ -> "union"
  | Periodic _ -> "periodic"
  | Sample _ -> "sample"
  | Alternate _ -> "alternate"
  | RTdelay _ -> "rtdelay"
  | CumulPeriodic _ -> "cumulperiodic"
  | AbsPeriodic _ -> "absperiodic"
  | FirstSampled _ -> "first_sampled"
  | LastSampled _ -> "last_sampled"
  | Forbid _ -> "forbid"
  | Allow _ -> "allow"
  | Sporadic _ -> "sporadic"
  | Pool (_, _) -> "pool"
  | DisjunctiveUnion _ -> "disjunctive union"
;;

(* | TimeVarRelation _ -> "time_var_rel"
  | IntParameterRelation _ -> "int_param_rel"
  | Distribution (_, d) -> String.cat (dist_name d) "distribution" *)

let clocks = function
  | Precedence { cause; conseq } | Causality { cause; conseq } -> [ cause; conseq ]
  | Exclusion (list, _) | Coincidence list -> list
  | Subclocking { sub; super; _ } -> [ sub; super ]
  | Minus { out; arg; except } -> out :: arg :: except
  | Delay { out; arg; base; _ } -> out :: arg :: Option.to_list base
  | Fastest { out; args } | Slowest { out; args } -> out :: args
  | Intersection { out; args } | Union { out; args } | DisjunctiveUnion { out; args; _ }
    -> out :: args
  | Periodic { out; base; _ } -> [ out; base ]
  | Sample { out; arg; base } -> [ out; arg; base ]
  | Alternate { first; second } -> [ first; second ]
  | RTdelay { out; arg; _ } -> [ out; arg ]
  | CumulPeriodic { out; _ } | AbsPeriodic { out; _ } -> [ out ]
  | FirstSampled { out; arg; base } | LastSampled { out; arg; base } -> [ out; arg; base ]
  | Forbid { from; until; args } | Allow { from; until; args } -> from :: until :: args
  | Sporadic { out; _ } -> [ out ]
  | Pool (_, list) ->
    let lock, unlock = List.split list in
    List.append lock unlock
;;

let map_time_const f = map_constr Fun.id Fun.id Fun.id f

module Specification = struct
  type ('c, 'tp, 'ip, 'tv, 'iv, 't) t =
    { duration : ('tv, 't) numeric_rel_constr list
    ; probabilistic : ('iv, 'tv, 't) probability_constr list
    ; logical : ('c, 'tp, 'ip, 'tv, 'iv, 't) constr list
    ; integer : ('iv, int) numeric_rel_constr list
    }
  [@@deriving map, show, fold]

  let empty = { duration = []; probabilistic = []; logical = []; integer = [] }

  let merge a b =
    { duration = List.append a.duration b.duration
    ; probabilistic = List.append a.probabilistic b.probabilistic
    ; logical = List.append a.logical b.logical
    ; integer = List.append a.integer b.integer
    }
  ;;

  let clocks s = List.flat_map clocks s.logical

  let length { duration; probabilistic; logical; integer } =
    List.length duration
    + List.length probabilistic
    + List.length logical
    + List.length integer
  ;;

  module Builder = struct
    type nonrec ('c, 'tp, 'ip, 'tv, 'iv, 't, 'gv) t =
      { mutable spec : ('c, 'tp, 'ip, 'tv, 'iv, 't) t }

    let make () = { spec = empty }
    let logical b c = b.spec <- { b.spec with logical = c :: b.spec.logical }
    let duration b c = b.spec <- { b.spec with duration = c :: b.spec.duration }
    let probab b c = b.spec <- { b.spec with probabilistic = c :: b.spec.probabilistic }
    let integer b c = b.spec <- { b.spec with integer = c :: b.spec.integer }

    let result b =
      { duration = List.rev b.spec.duration
      ; probabilistic = List.rev b.spec.probabilistic
      ; logical = List.rev b.spec.logical
      ; integer = List.rev b.spec.integer
      }
    ;;

    let empty_decl _ = ()

    let of_decl f =
      let spec = make () in
      f spec;
      result spec
    ;;

    let of_decl_with_output f =
      let spec = make () in
      let output = f spec in
      result spec, output
    ;;

    let of_stateful_decl state f =
      let spec = make () in
      let state = f state spec in
      state, result spec
    ;;

    let constraints_only constraints =
      let b = make () in
      List.iter (logical b) constraints;
      result b
    ;;
  end
end

module Module = struct
  type ('c, 'tp, 'ip, 'tv, 'iv, 't) t =
    { assumptions : ('c, 'tp, 'ip, 'tv, 'iv, 't) Specification.t list
    ; structure : ('c, 'tp, 'ip, 'tv, 'iv, 't) Specification.t
      (* WARNING: currently probability declarations inside structure are disallowed *)
    ; assertions : ('c, 'tp, 'ip, 'tv, 'iv, 't) Specification.t list
    }
  [@@deriving map, show, fold]

  let empty = { assumptions = []; structure = Specification.empty; assertions = [] }

  let make assumptions structure assertions =
    let open Specification.Builder in
    { assumptions = List.map of_decl assumptions
    ; structure = of_decl structure
    ; assertions = List.map of_decl assertions
    }
  ;;

  let make_stateful assumptions structure assertions state =
    let open Specification.Builder in
    let state, assumptions = List.fold_left_map of_stateful_decl state assumptions in
    let state, structure = of_stateful_decl state structure in
    let state, assertions = List.fold_left_map of_stateful_decl state assertions in
    state, { assumptions; structure; assertions }
  ;;

  let flatten { assumptions; structure; assertions } =
    let specs = structure :: List.append assumptions assertions in
    List.fold_left Specification.merge Specification.empty specs
  ;;

  let clocks { assumptions; structure; assertions } =
    List.flat_map Specification.clocks ((structure :: assumptions) @ assertions)
  ;;

  let length { assumptions; structure; assertions } =
    List.fold_left
      Int.add
      0
      (List.map Specification.length ((structure :: assumptions) @ assertions))
  ;;
end
