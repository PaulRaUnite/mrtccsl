open Language

module Macro = struct
  open Language.Specification.Builder
  open Trace

  let task_names name =
    let start = Printf.sprintf "%s.s" name in
    let finish = Printf.sprintf "%s.f" name in
    let release = Printf.sprintf "%s.r" name in
    let deadline = Printf.sprintf "%s.d" name in
    { name; release; start; finish; deadline }
  ;;

  let rigid_task name (exec_lower, exec_upper) builder =
    let exec_time = Printf.sprintf "%s.exec" name in
    let { start; finish; _ } = task_names name in
    logical builder @@ RTdelay { out = finish; arg = start; delay = Var exec_time };
    duration builder @@ NumRelation (exec_time, `MoreEq, Const exec_lower);
    duration builder @@ NumRelation (exec_time, `LessEq, Const exec_upper)
  ;;

  let task name exec_duration b =
    let { release; start; _ } = task_names name in
    logical b @@ Causality { cause = release; conseq = start };
    rigid_task name exec_duration b
  ;;

  let task_with_deadline name exec_duration deadline b =
    let finish = Printf.sprintf "%s.f" name in
    logical b @@ Precedence { cause = finish; conseq = deadline };
    task name exec_duration b
  ;;

  let rigid_periodic_task name exec_duration (period_lower, period_upper) offset b =
    let { start; _ } = task_names name in
    let error = Printf.sprintf "%s.error" name in
    logical b
    @@ CumulPeriodic
         { out = start; period = period_lower; error = Var error; offset = const offset };
    duration b @@ NumRelation (error, `MoreEq, const 0);
    duration b @@ NumRelation (error, `LessEq, const (period_upper - period_lower));
    rigid_task name exec_duration b
  ;;

  let periodic_task name exec_duration (period_lower, period_upper) offset b =
    let ready = Printf.sprintf "%s.r" name in
    let timer = Printf.sprintf "%s.t" name in
    let deadline = Printf.sprintf "%s.d" name in
    let error = Printf.sprintf "%s.error" name in
    logical b
    @@ CumulPeriodic
         { out = timer; period = period_lower; error = Var error; offset = const offset };
    duration b @@ NumRelation (error, `MoreEq, const 0);
    duration b @@ NumRelation (error, `LessEq, const (period_upper - period_lower));
    logical b @@ Delay { out = deadline; arg = timer; delay = const 1; base = timer };
    logical b @@ Coincidence [ timer; ready ];
    task_with_deadline name exec_duration deadline b
  ;;

  let scheduling_pairs tasks =
    List.map
      (fun name ->
         let { start; finish; _ } = task_names name in
         start, finish)
      tasks
  ;;
end

module SimpleControl = struct
  open Macro
  open Language.Specification

  let no_resource_constraint_rigid p_s e_s e_c p_a e_a b =
    rigid_periodic_task "s" e_s p_s 0 b;
    rigid_periodic_task "a" e_a p_a 0 b;
    rigid_task "c" e_c b;
    Builder.logical b @@ Coincidence [ "s.f"; "c.s" ]
  ;;

  let no_resource_constraint p_s e_s e_c b =
    periodic_task "s" e_s p_s 0 b;
    periodic_task "a" e_s p_s 0 b;
    task "c" e_c b;
    Builder.logical b @@ Coincidence [ "s.f"; "c.r" ];
    Builder.logical b @@ Alternate { first = "c.s"; second = "c.f"; strict = true }
  ;;

  let par_pipeline b =
    no_resource_constraint (48, 52) (5, 10) (25, 40) b;
    Builder.logical b @@ Alternate { first = "a.s"; second = "a.f"; strict = true };
    Builder.logical b @@ Alternate { first = "s.s"; second = "s.f"; strict = true };
    Builder.logical b @@ Alternate { first = "c.s"; second = "c.f"; strict = true }
  ;;

  let shared_2core b =
    Builder.logical b @@ Pool (2, scheduling_pairs [ "a"; "s"; "c" ]);
    (no_resource_constraint (48, 52) (5, 10) (25, 40)) b
  ;;

  let sa_group b =
    Builder.logical b @@ Pool (1, scheduling_pairs [ "a"; "s" ]);
    Builder.logical b @@ Pool (1, scheduling_pairs [ "c" ]);
    (no_resource_constraint (48, 52) (5, 10) (25, 40)) b
  ;;
end
