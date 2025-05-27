open Prelude
open Expr

type 'a interval = 'a * 'a [@@deriving map,show]

(*TODO: good expression type should:
  - differentiate rational, time and integer expressions types
  - clearly indicate when conversion happens?*)
type ('v, 'n) expr =
  | Var of 'v
  | Const of 'n
  | Bin of ('v, 'n) expr * num_op * ('v, 'n) expr
[@@deriving map,show]

let var v = Var v
let const c = Const c

(**RTCCSL constraint type. ['c] is clock variable type, ['p] is parameter variable type, ['n] numerical constraint type. *)
type ('c, 'p, 'v, 't) constr =
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
      ; delay : ('p, int) expr * ('p, int) expr
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
      ; period : ('p, int) expr
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
      ; delay : 'v
      }
  (* | Offset of
      { out : 'c
      ; delay : 'p
      } *)
  | CumulPeriodic of
      { out : 'c
      ; period : 'v
      ; offset : ('p, 't) expr
      }
  | AbsPeriodic of
      { out : 'c
      ; period : ('p, 't) expr
      ; error : 'v
      ; offset : ('p, 't) expr
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
      ; at_least : ('p, 't) expr
      ; strict : bool
      } (**Mutex is a special case of Pool where [n=1]*)
  | Pool of int * ('c * 'c) list
[@@deriving map, show]

(*TODO: replace rt.constraints with just delay and offset. *)
(* module Complex = struct
  let cumul_periodic out period_var offset_par = [ RTdelay { out; arg = out } ]
end *)

type ('p, 'v, 't) time_var_constr = TimeVarRelation of 'v * num_rel * ('p, 't) expr
[@@deriving map, show]

type ('c, 'p, 'v, 't) specification =
  { constraints : ('c, 'p, 'v, 't) constr list
  ; var_relations : ('p, 'v, 't) time_var_constr list
  }
[@@deriving map, show]

let empty = { constraints = []; var_relations = [] }
let constraints_only l = { constraints = l; var_relations = [] }

let merge
      { constraints = c1; var_relations = v1 }
      { constraints = c2; var_relations = v2 }
  =
  { constraints = List.append c1 c2; var_relations = List.append v1 v2 }
;;

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
;;

(* | TimeVarRelation _ -> "time_var_rel"
  | IntParameterRelation _ -> "int_param_rel"
  | Distribution (_, d) -> String.cat (dist_name d) "distribution" *)

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
  | Pool (_, list) ->
    let lock, unlock = List.split list in
    List.append lock unlock
;;

let spec_clocks s = List.flat_map clocks s.constraints
let map_time_const f = map_constr Fun.id Fun.id Fun.id f

module Examples = struct
  module Macro = struct
    let task_names name =
      let start = Printf.sprintf "%s.s" name in
      let finish = Printf.sprintf "%s.f" name in
      let ready = Printf.sprintf "%s.r" name in
      let deadline = Printf.sprintf "%s.d" name in
      name, ready, start, finish, deadline
    ;;

    let rigid_task name (exec_lower, exec_upper) =
      let exec_time = Printf.sprintf "%s.exec" name in
      let _, _, start, finish, _ = task_names name in
      { constraints = [ RTdelay { out = finish; arg = start; delay = exec_time } ]
      ; var_relations =
          [ TimeVarRelation (exec_time, MoreEq, const exec_lower)
          ; TimeVarRelation (exec_time, LessEq, const exec_upper)
          ]
      }
    ;;

    let task name exec_duration =
      let _, ready, start, _, _ = task_names name in
      merge
        { constraints = [ Causality { cause = ready; conseq = start } ]
        ; var_relations = []
        }
        (rigid_task name exec_duration)
    ;;

    let task_with_deadline name exec_duration deadline =
      let finish = Printf.sprintf "%s.f" name in
      merge
        { constraints = [ Precedence { cause = finish; conseq = deadline } ]
        ; var_relations = []
        }
        (task name exec_duration)
    ;;

    let rigid_periodic_task name exec_duration (period_lower, period_upper) offset =
      let _, _, start, _, _ = task_names name in
      let period = Printf.sprintf "%s.period" name in
      merge
        (rigid_task name exec_duration)
        { constraints = [ CumulPeriodic { out = start; period; offset = const offset } ]
        ; var_relations =
            [ TimeVarRelation (period, MoreEq, const period_lower)
            ; TimeVarRelation (period, LessEq, const period_upper)
            ]
        }
    ;;

    let periodic_task name exec_duration (period_lower, period_upper) offset =
      let ready = Printf.sprintf "%s.r" name in
      let timer = Printf.sprintf "%s.t" name in
      let deadline = Printf.sprintf "%s.d" name in
      let period = Printf.sprintf "%s.period" name in
      merge
        (task_with_deadline name exec_duration deadline)
        { constraints =
            [ CumulPeriodic { out = timer; period; offset = const offset }
            ; Delay
                { out = deadline
                ; arg = timer
                ; delay = const 1, const 1
                ; base = Some timer
                }
            ; Coincidence [ timer; ready ]
            ]
        ; var_relations =
            [ TimeVarRelation (period, MoreEq, const period_lower)
            ; TimeVarRelation (period, LessEq, const period_upper)
            ]
        }
    ;;

    let scheduling_pairs tasks =
      List.map
        (fun name ->
           let _, _, start, finish, _ = task_names name in
           start, finish)
        tasks
    ;;
  end

  module SimpleControl = struct
    open Macro

    let no_resource_constraint_rigid p_s e_s e_c p_a e_a =
      List.reduce_left
        merge
        Fun.id
        [ rigid_periodic_task "s" e_s p_s 0
        ; rigid_periodic_task "a" e_a p_a 0
        ; rigid_task "c" e_c
        ; constraints_only [ Coincidence [ "s.f"; "c.s" ] ]
        ]
    ;;

    let no_resource_constraint p_s e_s e_c =
      List.reduce_left
        merge
        Fun.id
        [ periodic_task "s" e_s p_s 0
        ; periodic_task "a" e_s p_s 0
        ; task "c" e_c
        ; constraints_only
            [ Coincidence [ "s.f"; "c.r" ]; Alternate { first = "c.s"; second = "c.f" } ]
        ]
    ;;

    let par_pipeline : (string, string, string, int) specification =
      List.reduce_left
        merge
        Fun.id
        [ { constraints =
              [ Alternate { first = "a.s"; second = "a.f" }
              ; Alternate { first = "s.s"; second = "s.f" }
              ; Alternate { first = "c.s"; second = "c.f" }
              ]
          ; var_relations = []
          }
        ; no_resource_constraint (48, 52) (5, 10) (25, 40)
        ]
    ;;

    let shared_2core : (string, string, string, int) specification =
      merge
        (constraints_only [ Pool (2, scheduling_pairs [ "a"; "s"; "c" ]) ])
        (no_resource_constraint (48, 52) (5, 10) (25, 40))
    ;;

    let sa_group : (string, string, string, int) specification =
      merge
        (constraints_only
           [ Pool (1, scheduling_pairs [ "a"; "s" ]); Pool (1, scheduling_pairs [ "c" ]) ])
        (no_resource_constraint (48, 52) (5, 10) (25, 40))
    ;;
  end
end
