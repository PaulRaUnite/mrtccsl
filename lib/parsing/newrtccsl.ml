type 'a inclusive_interval = 'a * 'a

type 'a interval =
  { left_strict : bool
  ; left : 'a
  ; right : 'a
  ; right_strict : bool
  }

(** Binary operation codes for numerical expressions. *)
type num_binop =
  [ `Add
  | `Sub
  | `Mul
  | `Div
  ]

(** Unary operations to convert from rationals to integers. *)
type r2i_cast =
  | Floor
  | Ceil

(** Integer expressions. *)
type ('v, 'r) iexpr =
  | IVar of 'v
  | IConst of int
  | IBinOp of ('v, 'r) iexpr * num_binop * ('v, 'r) iexpr
  | INeg of ('v, 'r) iexpr
  | ICast of r2i_cast * ('v, 'r) rexpr

(** Rational expressions. *)
and ('v, 'r) rexpr =
  | RVar of 'v
  | RConst of 'r
  | RBinOp of ('v, 'r) rexpr * num_binop * ('v, 'r) rexpr
  | RNeg of ('v, 'r) rexpr
  | RCast of ('v, 'r) iexpr
  | DDivDur of ('v, 'r) dexpr * ('v, 'r) dexpr

(** Duration expressions. *)
and ('v, 'r) dexpr =
  | DVar of 'v
  | DConst of 'r
  | DBinOp of ('v, 'r) dexpr * [ `Add | `Sub ] * ('v, 'r) dexpr
  | DMul of ('v, 'r) rexpr * ('v, 'r) dexpr
  | DDiv of ('v, 'r) dexpr * ('v, 'r) rexpr
  | DCastFromRat of ('v, 'r) rexpr (** rexpr s *)
  | DCastFromFreq of ('v, 'r) fexpr (** 1 / fexpr *)

(** Frequency expressions. *)
and ('v, 'r) fexpr =
  | FVar of 'v
  | FConst of 'r
  | FBinOp of ('v, 'r) fexpr * [ `Add | `Sub ] * ('v, 'r) fexpr
  | FMul of ('v, 'r) rexpr * ('v, 'r) fexpr
  | FDiv of ('v, 'r) fexpr * ('v, 'r) rexpr
  | FCastFromRat of ('v, 'r) rexpr (** rexpr Hz *)
  | FCastFromDur of ('v, 'r) dexpr (** 1 / dexpr *)

(** Auxiliary type for easier implementation if parameters are not supported, only constants. *)
type ('v, 'n) inline_param =
  | Param of 'v
  | Const of 'n

(** Comparisons allowed between the numerical expressions. *)
type num_comp =
  | Less (** < *)
  | LessEq (** <= *)
  | Eq (** == *)
  | More (** > *)
  | MoreEq (** >= *)
  | Neq (** != *)

(** Type of RTCCSL constraints, where ['v] is the variable type (clocks and parameters) and ['r] is the type of rationals. *)
type ('v, 'r) constr =
  | Precedence of
      { cause : 'v
      ; conseq : 'v
      }
  | Causality of
      { cause : 'v
      ; conseq : 'v
      }
  | Exclusion of 'v list
  | Coincidence of 'v list
  | Subclocking of
      { sub : 'v
      ; super : 'v
      }
  | Minus of
      { out : 'v
      ; arg : 'v
      ; except : 'v list
      }
  | Delay of
      { out : 'v
      ; arg : 'v
      ; delay : ('v, int) inline_param inclusive_interval
      ; base : 'v option
      }
  | Fastest of
      { out : 'v
      ; left : 'v
      ; right : 'v
      }
  | Slowest of
      { out : 'v
      ; left : 'v
      ; right : 'v
      }
  | Intersection of
      { out : 'v
      ; args : 'v list
      }
  | Union of
      { out : 'v
      ; args : 'v list
      }
  | Periodic of
      { out : 'v
      ; base : 'v
      ; period : ('v, int) inline_param
      }
  | Sample of
      { out : 'v
      ; arg : 'v
      ; base : 'v
      }
  | Alternate of
      { first : 'v
      ; second : 'v
      }
  | RTdelay of
      { out : 'v
      ; arg : 'v
      ; delay : ('v, 'r) inline_param interval
      }
  | CumulPeriodic of
      { out : 'v
      ; period : ('v, 'r) inline_param
      ; error : ('v, 'r) inline_param interval
      ; offset : ('v, 'r) inline_param interval
      }
  | AbsPeriodic of
      { out : 'v
      ; period : ('v, 'r) inline_param
      ; error : ('v, 'r) inline_param interval
      ; offset : ('v, 'r) inline_param interval
      }
  | FirstSampled of
      { out : 'v
      ; arg : 'v
      ; base : 'v
      }
  | LastSampled of
      { out : 'v
      ; arg : 'v
      ; base : 'v
      }
  | Forbid of
      { from : 'v
      ; until : 'v
      ; args : 'v list
      }
  | Allow of
      { from : 'v
      ; until : 'v
      ; args : 'v list
      }
  | Sporadic of
      { out : 'v
      ; at_least : ('v, 'r) inline_param
      ; strict : bool
      }
  | DisjUnion of
      { out : 'v
      ; args : 'v list
      }
  | Mutex of ('v * 'v) list
  | Pool of ('v, int) inline_param * ('v * 'v) list
  | IntComp of ('v, 'r) iexpr * num_comp * ('v, 'r) iexpr
  | RatComp of ('v, 'r) rexpr * num_comp * ('v, 'r) rexpr
  | DurComp of ('v, 'r) dexpr * num_comp * ('v, 'r) dexpr
  | FreqComp of ('v, 'r) fexpr * num_comp * ('v, 'r) fexpr

type ('v, 'r) specification = ('v, 'r) constr list

let clocks = function
  | Precedence { cause; conseq } | Causality { cause; conseq } -> [ cause; conseq ]
  | Exclusion list | Coincidence list -> list
  | Subclocking { sub; super } -> [ sub; super ]
  | Minus { out; arg; except } -> out :: arg :: except
  | Delay { out; arg; base; _ } -> out :: arg :: Option.to_list base
  | Fastest { out; left; right } | Slowest { out; left; right } -> [ out; left; right ]
  | Intersection { out; args } | Union { out; args } | DisjUnion { out; args } ->
    out :: args
  | Periodic { out; base; _ } -> [ out; base ]
  | Sample { out; arg; base } -> [ out; arg; base ]
  | Alternate { first; second } -> [ first; second ]
  | RTdelay { out; arg; _ } -> [ out; arg ]
  | CumulPeriodic { out; _ } | AbsPeriodic { out; _ } -> [ out ]
  | FirstSampled { out; arg; base } | LastSampled { out; arg; base } -> [ out; arg; base ]
  | Forbid { from; until; args } | Allow { from; until; args } -> from :: until :: args
  | Sporadic { out; _ } -> [ out ]
  | Mutex pairs | Pool (_, pairs) ->
    let locks, unlocks = List.split pairs in
    List.append locks unlocks
  | IntComp _ | RatComp _ | DurComp _ | FreqComp _ -> []
;;

type ('v, 'r) module_t =
  { assumptions : ('v, 'r) specification
  ; structure : ('v, 'r) specification
  ; assertion : ('v, 'r) specification
  ; interface : ('v, 'r) specification * ('v, 'r) specification
  }
(* type property_check = 
  type ('v, 'r) system =  *)
