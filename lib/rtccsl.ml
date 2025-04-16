open Prelude

type 'a interval = 'a * 'a

(*TODO: good expression type should:
  - differentiate rational, time and integer expressions types
  - clearly indicate when conversion happens?*)
type ('v, 'n) expr =
  | Var of 'v
  | Const of 'n
  | BinAdd of ('v, 'n) expr * ('v, 'n) expr
  | BinSub of ('v, 'n) expr * ('v, 'n) expr
  | BinMul of ('v, 'n) expr * ('v, 'n) expr
  | BinDiv of ('v, 'n) expr * ('v, 'n) expr

type 'v int_param =
  | IntVar of 'v
  | IntConst of int

type ('v, 't) time_param =
  | TimeVar of 'v
  | TimeConst of 't

type ('c, 'p, 't) constr =
  | Precedence of
      { cause : 'c
      ; conseq : 'c
      }
  | Causality of
      { cause : 'c
      ; conseq : 'c
      }
  | Exclusion of 'c list
  | Coincidence of 'c list
  | Subclocking of
      { sub : 'c
      ; super : 'c
      }
  | Minus of
      { out : 'c
      ; arg : 'c
      ; except : 'c list
      }
  | Delay of
      { out : 'c
      ; arg : 'c
      ; delay : 'p int_param interval
      ; base : 'c option
      }
  | Fastest of
      { out : 'c
      ; left : 'c
      ; right : 'c
      }
  | Slowest of
      { out : 'c
      ; left : 'c
      ; right : 'c
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
      ; period : 'p int_param
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
      ; delay : ('p, 't) time_param interval
      }
  | CumulPeriodic of
      { out : 'c
      ; period : ('p, 't) time_param
      ; error : ('p, 't) time_param interval
      ; offset : ('p, 't) time_param
      }
  | AbsPeriodic of
      { out : 'c
      ; period : ('p, 't) time_param
      ; error : ('p, 't) time_param interval
      ; offset : ('p, 't) time_param
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
      ; at_least : ('p, 't) time_param
      ; strict : bool
      }
  | TimeParameter of 'p * ('p, 't) expr interval
  | LogicalParameter of 'p * ('p, int) expr interval
  (**Encodes parameter [v] being inside of [[e1, e2]].*)
  (*TODO: strange name, why logical?*)
  | Pool of int * ('c * 'c) list
  (**Mutex is a special case of Pool where [n=1]*)

type ('c, 'p, 't) specification = ('c, 'p, 't) constr list

let clocks = function
  | Precedence { cause; conseq } | Causality { cause; conseq } -> [ cause; conseq ]
  | Exclusion list | Coincidence list -> list
  | Subclocking { sub; super } -> [ sub; super ]
  | Minus { out; arg; except } -> out :: arg :: except
  | Delay { out; arg; base; _ } -> out :: arg :: Option.to_list base
  | Fastest { out; left; right } | Slowest { out; left; right } -> [ out; left; right ]
  | Intersection { out; args } | Union { out; args } -> out :: args
  | Periodic { out; base; _ } -> [ out; base ]
  | Sample { out; arg; base } -> [ out; arg; base ]
  | Alternate { first; second } -> [ first; second ]
  | RTdelay { out; arg; _ } -> [ out; arg ]
  | CumulPeriodic { out; _ } | AbsPeriodic { out; _ } -> [ out ]
  | FirstSampled { out; arg; base } | LastSampled { out; arg; base } -> [ out; arg; base ]
  | Forbid { from; until; args } | Allow { from; until; args } -> from :: until :: args
  | Sporadic { out; _ } -> [ out ]
  | TimeParameter _ | LogicalParameter _ -> []
  | Pool (_, list) ->
    let lock, unlock = List.split list in
    List.append lock unlock
;;

let spec_clocks l = List.flat_map clocks l