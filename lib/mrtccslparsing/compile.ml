open Ppx_compare_lib.Builtin
open Prelude
open Number

type var =
  | Explicit of string list
  | Anonymous of int
[@@deriving compare]

let prefix prefix = function
  | Explicit list -> Explicit (prefix :: list)
  | Anonymous _ as a -> a
;;

type m = (var, var, var, var, var, Rational.t) Mrtccsl.Language.Module.t

type compile_error =
  | DuplicateDeclaration of
      { duplicate : Loc.location
      ; previous : Loc.location
      }
  | ComplexInlineDeclaration of Loc.location
  | WrongType of
      { call : Loc.location
      ; declaration : Loc.location
      }
  | IncorrectComparison of Loc.location
  | IncorrectValue of Loc.location * string
  | NotImplemented of string

type 'a with_error = ('a, compile_error) Result.t
type result = (m, compile_error list) Result.t

module Context = struct
  type head =
    | HExplicit of string
    | HAnonymous of int

  let head_to_var = function
    | HExplicit s -> Explicit [ s ]
    | HAnonymous a -> Anonymous a
  ;;

  let equal_head a b =
    match a, b with
    | HExplicit a, HExplicit b -> String.equal a b
    | HAnonymous a, HAnonymous b -> Int.equal a b
    | _ -> false
  ;;

  type var_decl =
    { var : head
    ; var_type : [ `Int | `Duration | `Clock ]
    ; location : Loc.location
    }

  type block =
    { id : string
    ; blocks : block list
    ; vars : var_decl list
    }

  let make_block id = { id; blocks = []; vars = [] }

  type t =
    { rev_roots : block list
    ; current : block option
    ; generator : int
    }

  let empty = { rev_roots = []; current = None; generator = 0 }

  let next_root context id =
    { rev_roots = Option.get context.current :: context.rev_roots
    ; current = Some { id; blocks = []; vars = [] }
    ; generator = context.generator
    }
  ;;

  let rec map_inplace f = function
    | [] -> Ok None
    | x :: xs ->
      (match f x with
       | Some (Ok y) -> Ok (Some (y :: xs))
       | Some (Error e) -> Error e
       | None ->
         Result.bind (map_inplace f xs) (fun o ->
           Ok (Option.bind o (fun xs -> Some (x :: xs)))))
  ;;

  let rec block_add ~block ~prefix decl : block with_error =
    let open Result.Syntax in
    match prefix with
    | x :: tail ->
      let f =
        fun block ->
        if String.equal block.id x
        then Some (block_add ~block ~prefix:tail decl)
        else None
      in
      let* blocks = map_inplace f block.blocks in
      let* blocks =
        match blocks with
        | Some blocks -> Ok blocks
        | None ->
          let* new_block = block_add ~block:(make_block x) ~prefix:tail decl in
          Ok (new_block :: block.blocks)
      in
      Ok { block with blocks }
    | [] ->
      (match List.find_opt (fun { var; _ } -> equal_head var decl.var) block.vars with
       | Some prev_decl ->
         Error
           (DuplicateDeclaration
              { duplicate = decl.location; previous = prev_decl.location })
       | None -> Ok { block with vars = decl :: block.vars })
  ;;

  let add ~context ~prefix decl : t with_error =
    let open Result.Syntax in
    let* current = block_add ~block:(Option.get context.current) ~prefix decl in
    Ok { context with current = Some current }
  ;;

  let add_variable ~context ~prefix variable var_type location : (t * var) with_error =
    let open Result.Syntax in
    let var = HExplicit variable in
    let* context = add ~context ~prefix { var; var_type; location } in
    Ok (context, Explicit (prefix @ [ variable ]))
  ;;

  let add_anon_variable ~context ~prefix ~var_type location : (t * var) with_error =
    let open Result.Syntax in
    let var = HAnonymous context.generator in
    let* context = add ~context ~prefix { var; var_type; location } in
    Ok ({ context with generator = context.generator + 1 }, Anonymous context.generator)
  ;;

  let rec search_block ~block ~expect ~location qualified_var : var with_error option =
    match qualified_var with
    | [ x ] ->
      (match List.find_opt (fun decl -> equal_head decl.var (HExplicit x)) block.vars with
       | Some decl ->
         if decl.var_type = expect
         then Some (Ok (head_to_var decl.var))
         else Some (Error (WrongType { call = decl.location; declaration = location }))
       | None -> None)
    | block_id :: path ->
      List.find_map
        (fun block ->
           if String.equal block.id block_id
           then
             search_block ~block ~expect ~location path
             |> Option.map (Result.map (prefix block_id))
           else None)
        block.blocks
    | [] -> failwith "empty variable"
  ;;

  let rec search ~context ~scope ~expect ~location qualified_var : var option with_error =
    match
      List.find_map
        (fun block ->
           search_block ~block ~expect ~location (List.append scope qualified_var))
        (Option.get context.current :: context.rev_roots)
    with
    | Some (Ok v) -> Ok (Some v)
    | Some (Error e) -> Error e
    | None ->
      (match scope with
       | _ :: scope -> search ~context ~scope ~expect ~location qualified_var
       | [] -> Ok None)
  ;;

  let resolve ~context ~scope ~expect (qualified_var : Ast.var) : (t * var) with_error =
    let open Result.Syntax in
    let Loc.{ data; loc = location } = qualified_var in
    let* result = search ~context ~scope ~expect ~location data in
    match result with
    | Some v -> Ok (context, v)
    | None ->
      (match qualified_var.data with
       | [] -> failwith "illegal variable: variable path cannot be empty"
       | v :: [] -> add_variable ~context ~prefix:scope v expect location
       | _ -> Error (ComplexInlineDeclaration location))
  ;;
end

open Ast

let into_module { assumptions; structure; assertions } =
  let open Mrtccsl.Language in
  let open Specification in
  let open Result.Syntax in
  let wrap_var v = Var v in
  let map_context_opt_result ~context f = function
    | Some x ->
      let* context, result = f ~context x in
      Ok (context, Some result)
    | None -> Ok (context, None)
  in
  let compile_int_expr ~context ~scope expr =
    match Loc.unwrap expr with
    (*TODO: write a simplification of the expressions? *)
    | IConstant c -> Ok (context, Const c)
    | IVariable v ->
      let* context, v = Context.resolve ~context ~scope ~expect:`Int v in
      Ok (context, wrap_var v)
    | IHole ->
      let* context, v =
        Context.add_anon_variable ~context ~prefix:scope ~var_type:`Int expr.loc
      in
      Ok (context, wrap_var v)
    | _ -> Error (NotImplemented "CCSL's IR does not support complex expressions")
  in
  let compile_duration (Second { value; scale }) = Number.Rational.mul value scale in
  let compile_duration_expr ~context ~scope expr =
    match Loc.unwrap expr with
    (*TODO: write a simplification of the expressions? *)
    | DConstant d -> Ok (context, Const (compile_duration d))
    | DVariable v ->
      let* context, v = Context.resolve ~context ~scope ~expect:`Int v in
      Ok (context, wrap_var v)
    | DHole ->
      let* context, v =
        Context.add_anon_variable ~context ~prefix:scope ~var_type:`Int expr.loc
      in
      Ok (context, wrap_var v)
    | _ -> Error (NotImplemented "CCSL's IR does not support complex expressions")
  in
  let compile_interval ~compile ~plus ~minus ~build ~context var expr =
    let* context, left_strict, left, right, right_strict =
      match expr with
      | Interval { left_strict; left; right; right_strict } ->
        let* context, left = compile ~context left in
        let* context, right = compile ~context right in
        Ok (context, left_strict, left, right, right_strict)
      | PlusMinus (mean, error) ->
        let* context, left = compile ~context (minus mean error) in
        let* context, right = compile ~context (plus mean error) in
        Ok (context, false, left, right, false)
    in
    build @@ NumRelation (var, (if left_strict then `More else `MoreEq), left);
    build @@ NumRelation (var, (if right_strict then `Less else `LessEq), right);
    Ok context
  in
  let compile_inline_relation ~compile ~plus ~minus ~expect ~build ~context ~scope expr =
    match Loc.unwrap expr with
    | InlineVariable v ->
      let* context, v = Context.resolve ~context ~scope ~expect v in
      Ok (context, wrap_var v)
    | InlineInterval interval ->
      let* context, v =
        Context.add_anon_variable ~context ~prefix:scope ~var_type:expect (Loc.where expr)
      in
      let* context = compile_interval ~compile ~plus ~minus ~build ~context v interval in
      Ok (context, wrap_var v)
  in
  let compile_integer_inline_relation ~context ~scope ~builder expr =
    let compile = compile_int_expr ~scope in
    let plus a b = Loc.wrap (IBinOp (a, `Add, b)) (Loc.bounding_box [ a; b ]) in
    let minus a b = Loc.wrap (IBinOp (a, `Sub, b)) (Loc.bounding_box [ a; b ]) in
    let build c = Builder.integer builder c in
    compile_inline_relation ~compile ~plus ~minus ~expect:`Int ~build ~context ~scope expr
  in
  let compile_duration_inline_relation ~context ~scope ~builder expr =
    let compile = compile_duration_expr ~scope in
    let plus a b = Loc.wrap (DBinOp (a, `Add, b)) (Loc.bounding_box [ a; b ]) in
    let minus a b = Loc.wrap (DBinOp (a, `Sub, b)) (Loc.bounding_box [ a; b ]) in
    let build c = Builder.duration builder c in
    compile_inline_relation ~compile ~plus ~minus ~expect:`Int ~build ~context ~scope expr
  in
  let rec compile_clock_expr ~context ~scope ~builder ~result_variable expr =
    let compile_clock_exprs context = compile_clock_exprs ~context ~scope ~builder in
    let* context, result_variable =
      match Loc.(expr.data) with
      | CVariable v -> Context.resolve ~context ~scope ~expect:`Clock v
      | _ ->
        Option.bind_else
          (Option.map (fun v -> Ok (context, v)) result_variable)
          (fun () ->
             Context.add_anon_variable
               ~context
               ~prefix:scope
               ~var_type:`Clock
               (Loc.where expr))
    in
    let out = result_variable in
    let* context =
      match Loc.unwrap expr with
      | CVariable _ -> Ok context
      | CIntersection args ->
        let* context, args = compile_clock_exprs context args in
        Builder.logical builder @@ Intersection { out; args };
        Ok context
      | CUnion args ->
        let* context, args = compile_clock_exprs context args in
        Builder.logical builder @@ Union { out; args };
        Ok context
      | CDisjUnion { args; ratios } ->
        let* context, args = compile_clock_exprs context args in
        let* context, ratios =
          map_context_opt_result ~context (Context.resolve ~scope ~expect:`Int) ratios
        in
        Builder.logical builder @@ DisjunctiveUnion { out; args; ratios };
        Ok context
      | CTickDelay { arg; delay; on } ->
        let* context, arg =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None arg
        in
        let* context, on =
          map_context_opt_result
            ~context
            (compile_clock_expr ~builder ~scope ~result_variable:None)
            on
        in
        let* context, delay =
          compile_integer_inline_relation ~context ~scope ~builder delay
        in
        Builder.logical builder @@ Delay { out; arg; delay; base = on };
        Ok context
      | CNext expr ->
        let* context, arg =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None expr
        in
        Builder.logical builder @@ Delay { out; arg; delay = Const 1; base = None };
        Ok context
      | CPeriodic { base; period; skip } ->
        let* context, base =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None base
        in
        let* context, period =
          compile_integer_inline_relation ~context ~scope ~builder period
        in
        let* context, skip =
          map_context_opt_result
            ~context
            (compile_integer_inline_relation ~builder ~scope)
            skip
        in
        Builder.logical builder @@ Periodic { out; base; period; skip };
        Ok context
      | CSample { arg; base } ->
        let* context, arg =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None arg
        in
        let* context, base =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None base
        in
        Builder.logical builder @@ Sample { out; arg; base };
        Ok context
      | CMinus { base; subs } ->
        let* context, base =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None base
        in
        let* context, subs = compile_clock_exprs context subs in
        Builder.logical builder @@ Minus { out; arg = base; except = subs };
        Ok context
      | CFastest args ->
        let* context, args = compile_clock_exprs context args in
        Builder.logical builder @@ Fastest { out; args };
        Ok context
      | CSlowest args ->
        let* context, args = compile_clock_exprs context args in
        Builder.logical builder @@ Slowest { out; args };
        Ok context
      | CPeriodJitter { period; error; offset } ->
        let period = compile_duration period in
        let* context, error =
          compile_duration_inline_relation ~context ~scope ~builder error
        in
        Builder.logical builder
        @@ AbsPeriodic
             { out
             ; period
             ; error
             ; offset =
                 Option.map_or
                   ~default:(const Rational.zero)
                   (compile_duration >> const)
                   offset
             };
        Ok context
      | CPeriodDrift { period; error; offset } ->
        let period = compile_duration period in
        let* context, error =
          compile_duration_inline_relation ~context ~scope ~builder error
        in
        Builder.logical builder
        @@ CumulPeriodic
             { out
             ; period
             ; error
             ; offset =
                 Option.map_or
                   ~default:(const Rational.zero)
                   (compile_duration >> const)
                   offset
             };
        Ok context
      | CTimeDelay { arg; delay } ->
        let* context, arg =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None arg
        in
        let* context, delay =
          compile_duration_inline_relation ~context ~scope ~builder delay
        in
        Builder.logical builder @@ RTdelay { out; arg; delay };
        Ok context
      | CSporadic { at_least; strict } ->
        let at_least = const (compile_duration at_least) in
        Builder.logical builder @@ Sporadic { out; at_least; strict };
        Ok context
    in
    Ok (context, result_variable)
  and compile_clock_exprs ~context ~scope ~builder (args : _ list) =
    List.fold_left_mapr
      (fun context expr ->
         compile_clock_expr ~context ~scope ~builder ~result_variable:None expr)
      context
      args
  in
  let compile_percentage ~context ~builder ~scope percentage location =
    let r100 = Rational.of_int 100 in
    if Rational.more percentage r100 || Rational.less percentage Rational.zero
    then Error (IncorrectValue (location, "icorrect percentage"))
    else (
      let to_ratio n =
        let nom, denom = Rational.to_mpzf2 n in
        let x = Mpzf.mul nom denom in
        Mpz.get_int x
      in
      let ratios =
        [ 0, to_ratio percentage; 1, to_ratio (Rational.sub r100 percentage) ]
      in
      let* context, var =
        Context.add_anon_variable ~context ~prefix:scope ~var_type:`Int location
      in
      Builder.probab builder @@ DiscreteProcess { name = var; ratios };
      Ok (context, var))
  in
  let rec compile_stmt ~context ~scope ~builder stmt =
    let* context = context in
    match Loc.unwrap stmt with
    | VariableDeclaration (var, expected_type) ->
      let* context, _ =
        Context.add_variable ~context ~prefix:scope var.data expected_type var.loc
      in
      Ok context
    | DurationRelation (left_ast, rights) ->
      let* context, left = compile_duration_expr ~context ~scope left_ast in
      let* context, _, _ =
        List.fold_left
          (fun state (comp, right_ast) ->
             let* context, left, left_ast = state in
             let* context, right = compile_duration_expr ~context ~scope right_ast in
             let* _ =
               match left, right with
               | Const cl, Const cr ->
                 if Expr.do_rel Number.Rational.compare comp cl cr
                 then Ok ()
                 else Error (IncorrectComparison (Loc.repack [ left_ast; right_ast ]).loc)
               | Const cl, Var v ->
                 Builder.duration builder (NumRelation (v, Expr.invert comp, Const cl));
                 Ok ()
               | Var v, x ->
                 Builder.duration builder (NumRelation (v, comp, x));
                 Ok ()
             in
             Ok (context, right, right_ast))
          (Ok (context, left, left_ast))
          rights
      in
      Ok context
    | IntRelation (left_ast, rights) ->
      let* context, left = compile_int_expr ~context ~scope left_ast in
      let* context, _, _ =
        List.fold_left
          (fun state (comp, right_ast) ->
             let* context, left, left_ast = state in
             let* context, right = compile_int_expr ~context ~scope right_ast in
             let* _ =
               match left, right with
               | Const cl, Const cr ->
                 if Expr.do_rel Int.compare comp cl cr
                 then Ok ()
                 else Error (IncorrectComparison (Loc.repack [ left_ast; right_ast ]).loc)
               | Const cl, Var v ->
                 Builder.integer builder (NumRelation (v, Expr.invert comp, Const cl));
                 Ok ()
               | Var v, x ->
                 Builder.integer builder (NumRelation (v, comp, x));
                 Ok ()
             in
             Ok (context, right, right_ast))
          (Ok (context, left, left_ast))
          rights
      in
      Ok context
    | ClockRelation (left, comp, right) ->
      let* context, left =
        compile_clock_expr ~context ~scope ~builder ~result_variable:None left
      in
      let result_variable =
        match comp with
        | Coincidence -> Some left
        | _ -> None
      in
      let* context, right =
        compile_clock_expr ~context ~scope ~result_variable ~builder right
      in
      let* context, percent_var =
        match comp with
        | Subclocking (Some (Percent percentage)) ->
          let* context, var =
            compile_percentage ~context ~builder ~scope percentage (Loc.where stmt)
          in
          Ok (context, Some var)
        | _ -> Ok (context, None)
      in
      let constr =
        match comp with
        | Coincidence -> Coincidence [ left; right ]
        | Exclusion -> Exclusion ([ left; right ], None)
        | Precedence -> Precedence { cause = left; conseq = right }
        | Causality -> Causality { cause = left; conseq = right }
        | Subclocking _ -> Subclocking { sub = left; super = right; dist = percent_var }
        | Alternation -> Alternate { first = left; second = right }
      in
      Builder.logical builder constr;
      Ok context
    | DiscreteProcess { var; values; ratios } ->
      let values = Loc.unwrap values
      and ratios = Loc.unwrap ratios in
      Builder.probab builder
      @@ DiscreteProcess
           { name = Explicit (Loc.unwrap var); ratios = List.combine values ratios };
      Ok context
    | ContinuousProcess { var; dist } ->
      Builder.probab builder
      @@ ContinuousProcess
           { name = Explicit (Loc.unwrap var)
           ; dist = map_distribution compile_duration (Loc.unwrap dist)
           };
      Ok context
    | Pool (n, pairs) ->
      let alloc, dealloc = List.split pairs in
      let* context, alloc = compile_clock_exprs ~context ~scope ~builder alloc in
      let* context, dealloc = compile_clock_exprs ~context ~scope ~builder dealloc in
      let pairs = List.combine alloc dealloc in
      Builder.logical builder @@ Pool (n, pairs);
      Ok context
    | Block { name; statements } ->
      compile_block
        ~scope:(List.append scope [ Loc.unwrap name ])
        ~context
        ~builder
        statements
  and compile_block ~scope ~context ~builder stmts =
    List.fold_left
      (fun context v -> compile_stmt ~context ~scope ~builder v)
      (Ok context)
      stmts
  in
  let compile_top_block name stmts context builder =
    let* context = context in
    let context = Context.next_root context name in
    compile_block ~scope:[] ~context ~builder stmts
  in
  let compile_top_blocks name list =
    List.mapi
      (fun i ->
         let name = Printf.sprintf "%s%d" name i in
         compile_top_block name)
      list
  in
  let context = Context.empty in
  Mrtccsl.Language.Module.make_stateful
    (compile_top_blocks "assume" assumptions)
    (compile_top_block "structure" structure)
    (compile_top_blocks "assert" assertions)
    (Ok context)
;;
