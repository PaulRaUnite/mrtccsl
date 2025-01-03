(* TODO: need to probably wrap the things to add metadata?*)
type location = Lexing.position * Lexing.position

type 'a loc =
  { metadata : location
  ; node : 'a
  }

let location_of_lex lex : location = Lexing.lexeme_start_p lex, Lexing.lexeme_end_p lex
let locate lex node = { node; metadata = location_of_lex lex }

type id = string Loc.t
type path = id list

type type_name =
  [ `Int
  | `Rational
  | `Time
  | `Interval of type_name
  | `Frequency
  | `Clock
  | `Block
  ]

type binop =
  | Add (* can be union or plus *)
  | Sub (* can be ccsl minus or not*)
  | Mul (* can be intersection or not*)
  | Div
  | DisjUnion

type unop =
  | Neg
  | Floor
  | Ceil

type arg_dec = id * type_name
type arg_declarations = arg_dec list

type num_rel =
  | Less (** < *)
  | LessEq (** <= *)
  | Eq (** = *)
  | More (** > *)
  | MoreEq (** >= *)
  | Neq (* != *)

type clock_rel =
  | Coincidence
  | Exclusion
  | Precedence
  | Causality
  | Subclocking
  | Alternation

type exn_rel =
  | OrCoincidence
  | OrPrecedence
  | OrCausality
  | XorCoincidence
  | XorPrecedence
  | XorCausality

type 'a interval =
  { left_strict : bool
  ; left : 'a
  ; right : 'a
  ; right_strict : bool
  }

type path_fragment =
  | Identifier of id
  | ModCall of
      { id : id
      ; args : expr list
      }

and variable_expr =
  | Dereference of
      { id : path_fragment list
      ; scope : int
      }

and num_expr = num_expr' Loc.t

and num_expr' =
  | IntConstant of int
  | RationalConstant of Rational.t
  | BinOp of num_expr * binop * num_expr
  | UnOp of unop * num_expr
  | Variable of variable_expr
  | SIUnit of
      { expr : num_expr
      ; scale : Rational.t
      ; into : [ `Time | `Frequency ]
      }
  | Hole

and interval_expr = interval_expr' Loc.t

and interval_expr' =
  | Variable of variable_expr
  | NegInterval of interval_expr
  | LeftBinOp of interval_expr * binop * num_expr
  | RightBinOp of num_expr * binop * interval_expr
  | Interval of num_expr interval
  | Singleton of num_expr

and clock_expr = clock_expr' Loc.t

and clock_expr' =
  | Variable of variable_expr
  | Intersection of
      { left : clock_expr
      ; right : clock_expr
      }
  | Union of
      { left : clock_expr
      ; right : clock_expr
      }
  | DisjUnion of
      { left : clock_expr
      ; right : clock_expr
      }
  | Delay of
      { arg : clock_expr
      ; delay : interval_expr
      ; on : clock_expr option
      }
  | Periodic of
      { base : clock_expr
      ; period : num_expr
      ; skip : num_expr
      }
  | Sample of
      { arg : clock_expr
      ; base : clock_expr
      }
  | Minus of
      { left : clock_expr
      ; right : clock_expr
      }
  | Fastest of clock_expr list
  | Slowest of clock_expr list
  | FirstSampled of
      { arg : clock_expr
      ; base : clock_expr
      }
  | LastSampled of
      { arg : clock_expr
      ; base : clock_expr
      }
  | CumulPeriodic of
      { period : num_expr
      ; error : interval_expr
      ; offset : interval_expr option
      }
  | AbsPeriodic of
      { period : num_expr
      ; error : interval_expr
      ; offset : interval_expr option
      }
  | RTDelay of
      { arg : clock_expr
      ; delay : interval_expr
      }
  | Sporadic of
      { at_least : num_expr
      ; strict : bool
      }

and block_expr = block_expr' Loc.t

and block_expr' =
  | Variable of variable_expr
  | Block of statements
  | Mutex of (expr * expr) list
  | Pool of int * (expr * expr) list

and expr =
  | WildcardVariable of variable_expr
  | NumExpr of num_expr
  | ClockExpr of clock_expr
  | IntervalExpr of expr interval
  | NumIntervalExpr of interval_expr
  | BlockExpr of block_expr

and statement = statement' Loc.t

and statement' =
  | NumRelation of num_expr * (num_rel * num_expr) list
  | ClockRelation of clock_expr * (clock_rel * clock_expr) list
  | ExtensibleRelation of clock_expr * exn_rel * clock_expr
  | BlockEquivalence of block_expr * block_expr
  | IntervalRelation of
      { arg : num_expr
      ; bounds : interval_expr
      }
  | Method of
      { name : id
      ; args : arg_declarations
      ; body : statements
      }
  | Allow of
      { inside : clock_expr interval
      ; clocks : clock_expr list
      }
  | Forbid of
      { inside : clock_expr interval
      ; clocks : clock_expr list
      }

and statements = statement list

type prop =
  | Schedulability
  | Finiteness
  | Liveness of
      { weak : bool
      ; exists : bool
      ; clocks : path list
      }

type toplevel =
  | ModuleDec of
      { name : id
      ; args : arg_declarations
      ; assumption : statements
      ; structure : statements
      ; assertion : statements
      ; upper_interface : statements
      ; lower_interface : statements
      }
  | Check of
      { params : id list
      ; stat : statement
      ; properties : prop list
      }

type file = toplevel list
