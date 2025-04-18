open Prelude

type 'a interval = 'a * 'a

type op =
  | Add
  | Sub
  | Mul
  | Div

(*TODO: good expression type should:
  - differentiate rational, time and integer expressions types
  - clearly indicate when conversion happens?*)
type ('v, 'n) expr =
  | Var of 'v
  | Const of 'n
  | Bin of ('v, 'n) expr * op * ('v, 'n) expr

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
  | Pool of int * ('c * 'c) list (**Mutex is a special case of Pool where [n=1]*)

type ('c, 'p, 't) specification = ('c, 'p, 't) constr list

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
  | TimeParameter (_, _) -> "time_param"
  | LogicalParameter (_, _) -> "int_param"
  | Pool (_, _) -> "pool"
;;

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

let int_param_map f = function
  | IntConst c -> IntConst c
  | IntVar v -> IntVar (f v)
;;

let time_param_map_const f = function
  | TimeVar v -> TimeVar v
  | TimeConst c -> TimeConst (f c)
;;

let rec expr_map fv fc = function
  | Var v -> Var (fv v)
  | Const c -> Const (fc c)
  | Bin (l, op, r) -> Bin (expr_map fv fc l, op, expr_map fv fc r)
;;

let map
      (type c nc p np t nt)
      (fc : c -> nc)
      (fp : p -> np)
      (fparam : (p, t) time_param -> (np, nt) time_param)
      (fexp : (p, t) expr -> (np, nt) expr)
      (c : (c, p, t) constr)
  : (nc, np, nt) constr
  =
  match c with
  | Precedence { cause; conseq } -> Precedence { cause = fc cause; conseq = fc conseq }
  | Causality { cause; conseq } -> Causality { cause = fc cause; conseq = fc conseq }
  | Exclusion list -> Exclusion (List.map fc list)
  | Coincidence list -> Coincidence (List.map fc list)
  | Subclocking { sub; super } -> Subclocking { sub = fc sub; super = fc super }
  | Minus { out; arg; except } ->
    Minus { out = fc out; arg = fc arg; except = List.map fc except }
  | Delay { out; arg; delay; base } ->
    Delay
      { out = fc out
      ; arg = fc arg
      ; delay = Tuple.map2 (int_param_map fp) delay
      ; base = Option.map fc base
      }
  | Fastest { out; left; right } ->
    Fastest { out = fc out; left = fc left; right = fc right }
  | Slowest { out; left; right } ->
    Slowest { out = fc out; left = fc left; right = fc right }
  | Intersection { out; args } -> Intersection { out = fc out; args = List.map fc args }
  | Union { out; args } -> Union { out = fc out; args = List.map fc args }
  | Periodic { out; base; period } ->
    Periodic { out = fc out; base = fc base; period = int_param_map fp period }
  | Sample { out; arg; base } -> Sample { out = fc out; arg = fc arg; base = fc base }
  | Alternate { first; second } -> Alternate { first = fc first; second = fc second }
  | RTdelay { out; arg; delay } ->
    let l, r = delay in
    RTdelay { out = fc out; arg = fc arg; delay = fparam l, fparam r }
  | CumulPeriodic { out; period; error; offset } ->
    let l, r = error in
    CumulPeriodic
      { out = fc out
      ; period = fparam period
      ; error = fparam l, fparam r
      ; offset = fparam offset
      }
  | AbsPeriodic { out; period; error; offset } ->
    let l, r = error in
    AbsPeriodic
      { out = fc out
      ; period = fparam period
      ; error = fparam l, fparam r
      ; offset = fparam offset
      }
  | FirstSampled { out; arg; base } ->
    FirstSampled { out = fc out; arg = fc arg; base = fc base }
  | LastSampled { out; arg; base } ->
    LastSampled { out = fc out; arg = fc arg; base = fc base }
  | Forbid { from; until; args } ->
    Forbid { from = fc from; until = fc until; args = List.map fc args }
  | Allow { from; until; args } ->
    Allow { from = fc from; until = fc until; args = List.map fc args }
  | Sporadic { out; at_least; strict } ->
    Sporadic { out = fc out; at_least = fparam at_least; strict }
  | TimeParameter (v, (l, r)) -> TimeParameter (fp v, (fexp l, fexp r))
  | LogicalParameter (v, (l, r)) ->
    LogicalParameter (fp v, (expr_map fp Fun.id l, expr_map fp Fun.id r))
  | Pool (n, pairs) -> Pool (n, List.map (Tuple.map2 fc) pairs)
;;

let map_time_const f = map Fun.id Fun.id (time_param_map_const f) (expr_map Fun.id f)

module Macro = struct
  let task_clocks name =
    let start = Printf.sprintf "%s.s" name in
    let finish = Printf.sprintf "%s.f" name in
    let ready = Printf.sprintf "%s.r" name in
    let deadline = Printf.sprintf "%s.d" name in
    name, ready, start, finish, deadline
  ;;

  let task name exec_duration =
    let _, ready, start, finish, _ = task_clocks name in
    [ Causality { cause = ready; conseq = start }
    ; RTdelay
        { out = finish
        ; arg = start
        ; delay = Tuple.map2 (fun x -> TimeConst x) exec_duration
        }
    ]
  ;;

  let task_with_deadline name exec_duration deadline =
    let finish = Printf.sprintf "%s.f" name in
    Precedence { cause = finish; conseq = deadline } :: task name exec_duration
  ;;

  let periodic_task name exec_duration period (nerror, perror) offset =
    let ready = Printf.sprintf "%s.r" name in
    let timer = Printf.sprintf "%s.t" name in
    let deadline = Printf.sprintf "%s.d" name in
    task_with_deadline name exec_duration deadline
    @ [ CumulPeriodic
          { out = timer
          ; period = TimeConst period
          ; error = TimeConst nerror, TimeConst perror
          ; offset = TimeConst offset
          }
      ; Delay
          { out = deadline
          ; arg = timer
          ; delay = IntConst 1, IntConst 1
          ; base = Some timer
          }
      ; Coincidence [ timer; ready ]
      ]
  ;;

  let scheduling_pairs tasks =
    List.map
      (fun name ->
         let _, _, start, finish, _ = task_clocks name in
         start, finish)
      tasks
  ;;
end

module Examples = struct
  open Macro

  module SimpleControl = struct
    let no_resource_constraint =
      List.flatten
        [ periodic_task "s" (10, 15) 50 (-2, 2) 0
        ; periodic_task "a" (5, 10) 50 (-2, 2) 0
        ; task "c" (25, 40)
        ; [ Coincidence [ "s.f"; "c.r" ]; Alternate { first = "c.s"; second = "c.f" } ]
        ]
    ;;

    let par_pipeline =
      List.flatten
        [ [ Alternate { first = "a.s"; second = "a.f" }
          ; Alternate { first = "s.s"; second = "s.f" }
          ; Alternate { first = "c.s"; second = "c.f" }
          ]
        ; no_resource_constraint
        ]
    ;;

    let shared_2core =
      Pool (2, scheduling_pairs [ "a"; "s"; "c" ]) :: no_resource_constraint
    ;;

    let sa_group =
      Pool (1, scheduling_pairs [ "a"; "s" ])
      :: Pool (1, scheduling_pairs [ "c" ])
      :: no_resource_constraint
    ;;
  end
end
