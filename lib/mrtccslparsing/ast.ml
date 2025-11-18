open Expr
open Number

type id = string Loc.t
type var = string list Loc.t
type clock = Clock
type percentage = Percent of Number.Rational.t

type duration =
  | Second of
      { value : Rational.t
      ; scale : Rational.t
      }

type 'n distribution =
  | DUniform
  | DNormal of
      { mean : 'n
      ; deviation : 'n
      }
  | DExponential of { mean : 'n }

type 'a interval =
  { left_strict : bool
  ; left : 'a
  ; right : 'a
  ; right_strict : bool
  }

type 'a numeric_interval =
  | Interval of 'a interval
  | PlusMinus of 'a * 'a

type 'a inline_relation' =
  | InlineExpr of 'a
  | InlineInterval of 'a numeric_interval

type 'a inline_relation = 'a inline_relation' Loc.t

type additive_union =
  | AUnion
  | ADisjunctiveUnion
[@@deriving compare]

type clock_rel =
  | Coincidence
  | Exclusion
  | Precedence
  | Causality
  | Subclocking of percentage option
  | Alternation

and contdist = duration distribution Loc.t

and duration_expr' =
  | DConstant of duration
  | DVariable of var
  | DBinOp of duration_expr * [ `Add | `Sub ] * duration_expr
  | DScaleOp of Rational.t * duration_expr
  | DNegation of duration_expr
  | DHole

and duration_expr = duration_expr' Loc.t

and int_expr' =
  | IConstant of int
  | IVariable of var
  | IBinOp of int_expr * num_op * int_expr
  | INegation of int_expr
  | IHole

and int_expr = int_expr' Loc.t

and clock_expr' =
  | CVariable of var
  | CIntersection of clock_expr list
  | CUnion of clock_expr list
  | CDisjUnion of
      { args : clock_expr list
      ; ratios : var option
      }
  | CTickDelay of
      { arg : clock_expr
      ; delay : int_expr inline_relation
      ; on : clock_expr option
      }
  | CNext of clock_expr
  | CPeriodic of
      { base : clock_expr
      ; period : int_expr inline_relation
      ; skip : int_expr inline_relation option
      }
  | CSample of
      { arg : clock_expr
      ; base : clock_expr
      }
  | CFirstSample of
      { arg : clock_expr
      ; base : clock_expr
      }
  | CLastSample of
      { arg : clock_expr
      ; base : clock_expr
      }
  | CMinus of
      { base : clock_expr
      ; subs : clock_expr list
      }
  | CFastest of clock_expr list
  | CSlowest of clock_expr list
  | CPeriodJitter of
      { period : duration
      ; error : duration_expr inline_relation
      ; offset : duration_expr option
      }
  | CPeriodDrift of
      { period : duration
      ; error : duration_expr inline_relation
      ; offset : duration_expr option
      }
  | CTimeDelay of
      { arg : clock_expr
      ; delay : duration_expr inline_relation
      }
  | CSporadic of
      { at_least : duration
      ; strict : bool
      }

and clock_expr = clock_expr' Loc.t

type var_type =
  [ `Int
  | `Duration
  | `Clock
  ]

type statement' =
  | VariableDeclaration of (id list * var_type) list
  | IntRelation of int_expr * (num_rel * int_expr) list
  | DurationRelation of duration_expr * (num_rel * duration_expr) list
  | ClockRelation of clock_expr * clock_rel * clock_expr
  | AdditiveUnion of var * additive_union * clock_expr
  | DiscreteProcess of
      { var : var
      ; values : int list Loc.t
      ; ratios : int list Loc.t
      }
  | ContinuousProcess of
      { var : var
      ; dist : contdist
      }
  | Pool of int * (clock_expr * clock_expr) list
  | Block of
      { name : id
      ; statements : statements
      }
  | Allow of
      { clocks : clock_expr list
      ; interval : clock_expr interval
      }
  | Forbid of
      { clocks : clock_expr list
      ; interval : clock_expr interval
      }

and statement = statement' Loc.t
and statements = statement list

type module_body_declaration =
  { assumptions : statements list
  ; structure : statements
  ; assertions : statements list
  }

type id_types =
  [ `Duration
  | `Int
  | `Block
  | `Clock
  ]
