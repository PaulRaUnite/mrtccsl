type 'a interval = 'a * 'a

(** Binary operation codes for numerical expressions. *)
type num_binop =
  | Add
  | Sub
  | Mul
  | Div

(** Unary operation codes for numerical expressions. *)
type num_unop =
  | Neg
  | Floor
  | Ceil

(** Type of numerical expressions with type holes for ['v] variables and ['n] number constraints. *)
type ('v, 'n) expr =
  | Var of 'v
  | Const of 'n
  | BinOp of ('v, 'n) expr * num_binop * ('v, 'n) expr
  | UnOp of num_unop * ('v, 'n) expr

(** Auxiliary type for easier implementation if parameters are not supported, only constants. *)
type ('v, 'n) inline_param =
  | VarParam of 'v
  | ConstParam of 'n

(** Comparisons allowed between the numerical expressions. *)
type num_comp =
  | Less (** < *)
  | LessEq (** <= *)
  | Eq (** = *)
  | More (** > *)
  | MoreEq (** >= *)

(** Type of RTCCSL constraints, where ['v] is variable type (clocks and parameters) and ['r] is for type of rationals. *)
type ('v, 'r) constr =
  | Precedence of
      { cause : 'v
      ; effect : 'v
      }
  | Causality of
      { cause : 'v
      ; effect : 'v
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
      ; delay : ('v, int) inline_param interval
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
      ; offset : ('v, 'r) inline_param
      }
  | AbsPeriodic of
      { out : 'v
      ; period : ('v, 'r) inline_param
      ; error : ('v, 'r) inline_param interval
      ; offset : ('v, 'r) inline_param
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
  | NumComp of ('v, 'r) expr * num_comp * ('v, 'r) expr (** Encodes relations of *)

type ('v, 'r) specification = ('v, 'r) constr list

let clocks = function
  | Precedence { cause; effect } | Causality { cause; effect } -> [ cause; effect ]
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
  | NumComp _ -> []
;;
