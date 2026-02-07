open Prelude
open Expr

(** Constraint definitions and supporing functions. *)
module Cstr = struct
  (** Type of constraint arguments. *)
  type ('v, 'n) arg =
    | Var of 'v
    | Const of 'n
  [@@deriving map, show, fold]

  (** Constructs variable/parameter argument. *)
  let var v = Var v

  (** Constructs constant argument. *)
  let const c = Const c

  (** Rewrites the argument by using [var] and [const] functions. *)
  let unwrap_arg : 'a 'b 'c. var:('a -> 'b) -> const:('c -> 'b) -> ('a, 'c) arg -> 'b =
    fun ~var ~const arg ->
    match arg with
    | Var v -> var v
    | Const c -> const c
  ;;

  (** Clock constraint type. ['c] is clock variable symbols type, ['_p] is parameter (unchanged during execution) symbols type (['tp] is for durations, ['ip] is for integers), ['_v] is symbol type for variables (change during execution), ['t] is the type of duration constants. *)
  type ('c, 'tp, 'ip, 'tv, 'iv, 't) clock_constr =
    | Precedence of
        { cause : 'c
        ; conseq : 'c
        }
    | Causality of
        { cause : 'c
        ; conseq : 'c
        }
    | Exclusion of
        { args : 'c list
        ; choice : 'iv option
        }
    | Coincidence of 'c list
    | Subclocking of
        { sub : 'c
        ; super : 'c
        ; choice : 'iv option
        }
    | Minus of
        { out : 'c
        ; arg : 'c
        ; except : 'c list
        }
    | Delay of
        { out : 'c
        ; arg : 'c
        ; delay : ('iv, int) arg
        ; base : 'c
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
        ; period : int
        ; error : ('iv, int) arg
        ; offset : ('ip, int) arg
        }
    | Sample of
        { out : 'c
        ; arg : 'c
        ; base : 'c
        }
    | Alternate of
        { first : 'c
        ; second : 'c
        ; strict : bool
        }
    | RTdelay of
        { out : 'c
        ; arg : 'c
        ; delay : ('tv, 't) arg
        }
    (* | Offset of
      { out : 'c
      ; delay : 'p
      } *)
    | CumulPeriodic of
        { out : 'c
        ; period : 't
        ; error : ('tv, 't) arg
        ; offset : ('tp, 't) arg
        }
    | AbsPeriodic of
        { out : 'c
        ; period : 't
        ; error : ('tv, 't) arg
        ; offset : ('tp, 't) arg
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
        { left : 'c
        ; right : 'c
        ; args : 'c list
        }
    | Allow of
        { left : 'c
        ; right : 'c
        ; args : 'c list
        }
    | Sporadic of
        { out : 'c
        ; at_least : ('tp, 't) arg
        }
    | Pool of int * ('c * 'c) list (** Mutex is a special case of Pool where [n=1] *)
    | DisjunctiveUnion of
        { out : 'c
        ; args : 'c list
        ; choice : 'iv option
        }
  [@@deriving map, show, fold]

  let to_string c tp ip tv iv t constr =
    let pp to_string fmt v = Format.fprintf fmt "%s" (to_string v) in
    Format.asprintf
      "%a"
      (pp_clock_constr (pp c) (pp tp) (pp ip) (pp tv) (pp iv) (pp t))
      constr
  ;;

  (* TODO: add some sort of universal assumptions on the constraint definition/arguments?
  Maybe it is possible to extract them from the bounds in Rocq?
  It also should be possible to translate them to the domain on which the constraints are actually defined. *)

  (** Defines constraint argument assumptions. Currently only checks for wrong usage of logical clocks. *)
  let argument_assumptions = function
    | Fastest { args; _ }
    | Slowest { args; _ }
    | Intersection { args; _ }
    | Union { args; _ } -> not (List.is_empty args)
    | _ -> true
  ;;

  (* TODO: replace rt.constraints with just delay and offset. *)
  (* TODO: redefine some constraint in terms of others or at least provide the tautologies. *)

  (** Numerical relation constraint, represents ['v |><| ('v | 'c)] relation, where ['v] is variable type and ['c] is constant type. *)
  type ('v, 'c) numeric_rel_constr = NumRelation of 'v * num_rel * ('v, 'c) arg
  [@@deriving map, show, fold]

  (** Variants of continuous-valued distributions that can be used in a simulation. *)
  type 'n distribution =
    | Uniform
    | Normal of
        { mean : 'n
        ; deviation : 'n
        }
    | Exponential of { rate : 'n }
  [@@deriving map, show, fold]

  (** Constraint that binds a distribution to variable ['iv] or ['tv]. *)
  type ('iv, 'tv, 't) probability_constr =
    | DiscreteValued of
        { name : 'iv
        ; ratios : (int * int) list
        }
      (* ratios provide the distribution function *)
    | ContinuousValued of
        { name : 'tv
        ; dist : 't distribution
        }
  [@@deriving map, show, fold]

  (** Clock constraint name. *)
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

  (** Lists all constraint clocks. *)
  let clocks = function
    | Precedence { cause; conseq } | Causality { cause; conseq } -> [ cause; conseq ]
    | Exclusion { args; _ } | Coincidence args -> args
    | Subclocking { sub; super; _ } -> [ sub; super ]
    | Minus { out; arg; except } -> out :: arg :: except
    | Delay { out; arg; base; _ } -> [ out; arg; base ]
    | Fastest { out; args } | Slowest { out; args } -> out :: args
    | Intersection { out; args } | Union { out; args } | DisjunctiveUnion { out; args; _ }
      -> out :: args
    | Periodic { out; base; _ } -> [ out; base ]
    | Sample { out; arg; base } -> [ out; arg; base ]
    | Alternate { first; second; _ } -> [ first; second ]
    | RTdelay { out; arg; _ } -> [ out; arg ]
    | CumulPeriodic { out; _ } | AbsPeriodic { out; _ } -> [ out ]
    | FirstSampled { out; arg; base } | LastSampled { out; arg; base } ->
      [ out; arg; base ]
    | Forbid { left; right; args; _ } | Allow { left; right; args; _ } ->
      left :: right :: args
    | Sporadic { out; _ } -> [ out ]
    | Pool (_, list) ->
      let lock, unlock = List.split list in
      List.append lock unlock
  ;;

  (** Maps only the time constants in a logical constraint. *)
  let map_time_const f = map_clock_constr Fun.id Fun.id Fun.id f
end

(** Module of specifications. *)
module Specification = struct
  open Cstr

  (** Specification type, lists all types of constraints. *)
  type ('c, 'tp, 'ip, 'tv, 'iv, 't) t =
    { duration : ('tv, 't) numeric_rel_constr list
    ; probabilistic : ('iv, 'tv, 't) probability_constr list
    ; clock : ('c, 'tp, 'ip, 'tv, 'iv, 't) clock_constr list
    ; integer : ('iv, int) numeric_rel_constr list
    }
  [@@deriving map, show, fold]

  (** Empty specification. *)
  let empty = { duration = []; probabilistic = []; clock = []; integer = [] }

  (** Merges two specifications, the corresponding constraints are simply listed together. *)
  let merge a b =
    { duration = List.append a.duration b.duration
    ; probabilistic = List.append a.probabilistic b.probabilistic
    ; clock = List.append a.clock b.clock
    ; integer = List.append a.integer b.integer
    }
  ;;

  (** Lists all present clocks in the specification. Clocks may repeat. *)
  let clocks s = List.flat_map clocks s.clock

  (** Number of constraints (of any type) in the specification. *)
  let length { duration; probabilistic; clock; integer } =
    List.length duration
    + List.length probabilistic
    + List.length clock
    + List.length integer
  ;;

  (** Adds only the clock constraints in the specification. *)
  let clock_constraints_only constraints =
    { clock = constraints; duration = []; probabilistic = []; integer = [] }
  ;;

  (** Helper module for constructing specifications in imperative style. *)
  module Builder = struct
    (** Reexport of the specification type. *)
    type ('c, 'tp, 'ip, 'tv, 'iv, 't) spec = ('c, 'tp, 'ip, 'tv, 'iv, 't) t

    (** Builder type. *)
    type nonrec ('c, 'tp, 'ip, 'tv, 'iv, 't) t =
      { mutable spec : ('c, 'tp, 'ip, 'tv, 'iv, 't) t }

    (** Creates a builder with empty specification. *)
    let make () = { spec = empty }

    (** Adds logical constraint to the specification. *)
    let logical b c = b.spec <- { b.spec with clock = c :: b.spec.clock }

    (** Adds time duration relation constraint to the specification. *)
    let duration b c = b.spec <- { b.spec with duration = c :: b.spec.duration }

    (** Adds probabilistic constraint to the specification. *)
    let probab b c = b.spec <- { b.spec with probabilistic = c :: b.spec.probabilistic }

    (** Adds integer relation constraint to the specification. *)
    let integer b c = b.spec <- { b.spec with integer = c :: b.spec.integer }

    (** Returns specification with the added constraints in the push order. *)
    let get b =
      { duration = List.rev b.spec.duration
      ; probabilistic = List.rev b.spec.probabilistic
      ; clock = List.rev b.spec.clock
      ; integer = List.rev b.spec.integer
      }
    ;;

    (** Declaration is a function that adds the builder with constraints. *)
    type ('c, 'tp, 'ip, 'tv, 'iv, 't) decl = ('c, 'tp, 'ip, 'tv, 'iv, 't) t -> unit

    let empty_decl _ = ()

    (** Returns the specification defined using a declaration function. *)
    let of_decl (f : _ decl) : _ spec =
      let spec = make () in
      f spec;
      get spec
    ;;

    (** Stateful declaration is a function that adds the builder with constraints while capturing and returning some state. *)
    type ('s, 'c, 'tp, 'ip, 'tv, 'iv, 't) stateful_decl =
      's -> ('c, 'tp, 'ip, 'tv, 'iv, 't) t -> 's

    let of_stateful_decl state (f : _ stateful_decl) : _ * _ spec =
      let spec = make () in
      let state = f state spec in
      state, get spec
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
