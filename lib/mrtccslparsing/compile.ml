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
      { duplicate : Loc.location * Ast.var_type
      ; previous : Loc.location * Ast.var_type
      }
  | ComplexInlineVariableDeclaration of Loc.location
  | WrongUsageType of
      { call : Loc.location * Ast.var_type
      ; declaration : Loc.location * Ast.var_type
      }
  | IncorrectComparison of Loc.location
  | IncorrectValue of Loc.location * string
  | NotImplemented of Loc.location * string

let red = Ocolor_types.C4 Ocolor_types.red
let yellow = Ocolor_types.C4 Ocolor_types.yellow
let green = Ocolor_types.C4 Ocolor_types.green
let blue = Ocolor_types.C4 Ocolor_types.hi_blue

let type_to_string = function
  | `Int -> "integer"
  | `Duration -> "duration"
  | `Clock -> "clock"
;;

let print_compile_error fmt =
  let print_msg color fmt msg =
    Ocolor_format.pp_open_style fmt (Ocolor_types.Fg color);
    Format.fprintf fmt "%s\n" msg;
    Ocolor_format.pp_close_style fmt ()
  in
  function
  | DuplicateDeclaration { duplicate = dloc, dtype; previous = ploc, ptype } ->
    print_msg red fmt "Error: Inconsistent variable declaration.";
    Loc.highlight
      ~color:red
      ~symbol:'^'
      dloc
      (Format.sprintf "variable is declared as %s" (type_to_string dtype))
      fmt;
    Format.fprintf fmt "\n";
    Loc.highlight
      ~color:blue
      ~symbol:'-'
      ploc
      (Format.sprintf "but variable was declared as %s." (type_to_string ptype))
      fmt
  | ComplexInlineVariableDeclaration loc ->
    print_msg red fmt "Allocating complex variables is not supported.";
    Loc.highlight
      ~color:red
      ~symbol:'^'
      loc
      "verify that this variable was correctly declared before"
      fmt
  | WrongUsageType { call = cloc, ctype; declaration = dloc, dtype } ->
    print_msg red fmt "Inconsistency between previous and current usage of a variable.";
    Loc.highlight
      ~color:red
      ~symbol:'^'
      cloc
      (Format.sprintf "variable is used in %s context" (type_to_string ctype))
      fmt;
    Loc.highlight
      ~color:blue
      ~symbol:'-'
      dloc
      (Format.sprintf "but it was declared as %s" (type_to_string dtype))
      fmt
  | IncorrectComparison loc ->
    print_msg red fmt "Ahead-of-time comparison check failed.";
    Loc.highlight
      ~color:red
      ~symbol:'^'
      loc
      (Format.sprintf "this relation never evaluate to true")
      fmt
  | IncorrectValue (loc, msg) ->
    print_msg red fmt "Value convertion failed.";
    Loc.highlight ~color:red ~symbol:'^' loc msg fmt
  | NotImplemented (loc, msg) ->
    print_msg red fmt "Feature is not implemented.";
    Loc.highlight
      ~color:red
      ~symbol:'^'
      loc
      (Format.sprintf "not implemented, %s." msg)
      fmt
;;

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

  let pp_var fmt { var; var_type; _ } =
    let var_string =
      match var with
      | HExplicit s -> s
      | HAnonymous i -> Format.sprintf "anon(%i)" i
    in
    Format.fprintf fmt "%s: %s;" var_string (type_to_string var_type)
  ;;

  type block =
    { id : string
    ; blocks : block list
    ; vars : var_decl list
    }

  let rec pp_block fmt ~indent { id; blocks; vars } =
    let pp_sep fmt () = Format.fprintf fmt "\n" in
    let pp_indent f fmt v =
      Format.fprintf fmt "%s%a" (String.repeat " " (indent + 4)) f v
    in
    Format.fprintf fmt "%s {\n" id;
    Format.pp_print_list ~pp_sep (pp_indent pp_var) fmt (List.rev vars);
    if not (List.is_empty vars) then Format.pp_print_newline fmt ();
    Format.pp_print_list
      ~pp_sep
      (pp_indent (pp_block ~indent:(indent + 4)))
      fmt
      (List.rev blocks);
    if not (List.is_empty blocks) then Format.pp_print_newline fmt ();
    Format.fprintf fmt "%s} " (String.repeat " " indent)
  ;;

  let make_block id = { id; blocks = []; vars = [] }

  module VarMap = Map.Make (struct
      type t = Ast.additive_union * string list

      let compare =
        Tuple.compare2 Ast.compare_additive_union (List.compare String.compare)
      ;;
    end)

  type t =
    { rev_roots : block list
    ; current : (block * var list VarMap.t) option
    ; generator : int
    }

  let pp fmt { rev_roots; current; _ } =
    let blocks =
      match current with
      | Some (current, _) -> current :: rev_roots
      | None -> rev_roots
    in
    Format.fprintf
      fmt
      "%a@."
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt "")
         (pp_block ~indent:0))
      (List.rev blocks)
  ;;

  let empty = { rev_roots = []; current = None; generator = 0 }

  let next_root context id =
    { rev_roots =
        Option.map_or (fun (x, _) -> x :: context.rev_roots) ~default:[] context.current
    ; current = Some ({ id; blocks = []; vars = [] }, VarMap.empty)
    ; generator = context.generator
    }
  ;;

  (** Extracts additive constraints as regular constraints from the current context. *)
  let extract_additive_constraints context builder =
    let constraints =
      match context.current with
      | Some (_, map) ->
        map
        |> VarMap.to_list
        |> List.map (fun ((t, v), args) ->
          match t with
          | Ast.AUnion -> Mrtccsl.Language.Cstr.Union { out = Explicit v; args }
          | Ast.ADisjunctiveUnion ->
            Mrtccsl.Language.Cstr.DisjunctiveUnion
              { out = Explicit v; args; choice = None })
      | None -> []
    in
    List.iter (Mrtccsl.Language.Specification.Builder.logical builder) constraints
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
       | Some prev_decl when prev_decl.var_type <> decl.var_type ->
         Error
           (DuplicateDeclaration
              { duplicate = decl.location, decl.var_type
              ; previous = prev_decl.location, prev_decl.var_type
              })
       | _ -> Ok { block with vars = decl :: block.vars })
  ;;

  let add ~context ~prefix decl : t with_error =
    let open Result.Syntax in
    let block, additive_map = Option.get context.current in
    let* current = block_add ~block ~prefix decl in
    Ok { context with current = Some (current, additive_map) }
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
         else
           Some
             (Error
                (WrongUsageType
                   { call = location, expect; declaration = decl.location, decl.var_type }))
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
        ((fst @@ Option.get context.current) :: context.rev_roots)
    with
    | Some (Ok v) -> Ok (Some v)
    | Some (Error e) -> Error e
    | None ->
      (match List.last_partition scope with
       | Some _, scope -> search ~context ~scope ~expect ~location qualified_var
       | _ -> Ok None)
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
       | _ -> Error (ComplexInlineVariableDeclaration location))
  ;;

  let resolve_local ~context ~scope ~expect (qualified_var : Ast.var)
    : (t * var) with_error
    =
    let open Result.Syntax in
    let* new_context, v =
      resolve ~context:{ context with rev_roots = [] } ~scope ~expect qualified_var
    in
    Ok ({ new_context with rev_roots = context.rev_roots }, v)
  ;;

  let additive_constraint ~context (var : var) (t : Ast.additive_union) (e : var) : t =
    let block, map = Option.get context.current in
    let var =
      match var with
      | Explicit list -> list
      | Anonymous _ ->
        failwith "additive constraints can only use explicit clocks (not anonymous)"
    in
    let map = VarMap.entry ~default:[] (List.cons e) (t, var) map in
    { context with current = Some (block, map) }
  ;;
end

open Ast

let error_recover ~context ~errors = function
  | Ok context -> context, []
  | Error e -> context, e :: errors
;;

let[@inline] accumulate_errors ~errors (context, new_errors) =
  context, List.append new_errors errors
;;

let[@inline] finilize_errors (context, errors) = context, List.rev errors

(* TODO: add pruning for anonymous coincidence constraints: if there are anon variables in coincidence, substitute them with proper variable or choose only one and remove the constraint. Should allow to use chain coincidence. *)

let into_module { assumptions; structure; assertions } =
  let open Mrtccsl.Language in
  let open Cstr in
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
    | _ ->
      Error
        (NotImplemented
           (Loc.where expr, "CCSL's IR does not support complex integer expressions"))
  in
  let compile_duration (Second { value; scale }) = Number.Rational.mul value scale in
  let compile_distribution =
    let open Ast in
    function
    | DUniform -> Uniform
    | DNormal { mean; deviation } ->
      Normal { mean = compile_duration mean; deviation = compile_duration deviation }
    | DExponential { mean } ->
      Exponential { rate = Rational.(one / compile_duration mean) }
  in
  let compile_duration_expr ~context ~scope expr =
    match Loc.unwrap expr with
    (*TODO: write a simplification of the expressions? *)
    | DConstant d -> Ok (context, Const (compile_duration d))
    | DVariable v ->
      let* context, v = Context.resolve ~context ~scope ~expect:`Duration v in
      Ok (context, wrap_var v)
    | DHole ->
      let* context, v =
        Context.add_anon_variable ~context ~prefix:scope ~var_type:`Duration expr.loc
      in
      Ok (context, wrap_var v)
    | _ ->
      Error
        (NotImplemented
           (Loc.where expr, "CCSL's IR does not support complex duration expressions"))
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
    | InlineExpr e ->
      let* context, v = compile ~context e in
      Ok (context, v)
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
          (fun () ->
             Context.add_anon_variable
               ~context
               ~prefix:scope
               ~var_type:`Clock
               (Loc.where expr))
          (Option.map (fun v -> Ok (context, v)) result_variable)
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
        let* context, choice =
          map_context_opt_result ~context (Context.resolve ~scope ~expect:`Int) ratios
        in
        Builder.logical builder @@ DisjunctiveUnion { out; args; choice };
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
        Builder.logical builder
        @@ Delay { out; arg; delay; base = Option.value ~default:arg on };
        Ok context
      | CNext expr ->
        let* context, arg =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None expr
        in
        Builder.logical builder @@ Delay { out; arg; delay = Const 1; base = arg };
        Ok context
      | CPeriodic { base; period; error; offset } ->
        let* context, base =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None base
        in
        if Loc.unwrap period < 1
        then
          Error
            (IncorrectValue
               (Loc.where period, "period argument should be bigger than zero"))
        else
          let* context, error =
            compile_integer_inline_relation ~context ~scope ~builder error
          in
          let* context, offset =
            map_context_opt_result
              ~context
              (compile_integer_inline_relation ~builder ~scope)
              offset
          in
          Builder.logical builder
          @@ Periodic
               { out
               ; base
               ; period = Loc.unwrap period
               ; error
               ; offset = Option.value ~default:(const 0) offset
               };
          Ok context
      | (CSample { arg; base } | CFirstSample { arg; base } | CLastSample { arg; base })
        as c ->
        let* context, arg =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None arg
        in
        let* context, base =
          compile_clock_expr ~context ~scope ~builder ~result_variable:None base
        in
        (match c with
         | CSample _ -> Builder.logical builder @@ Sample { out; arg; base }
         | CFirstSample _ -> Builder.logical builder @@ FirstSampled { out; arg; base }
         | CLastSample _ -> Builder.logical builder @@ LastSampled { out; arg; base }
         | _ -> failwith "impossible");
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
        let* context, offset =
          map_context_opt_result ~context (compile_duration_expr ~scope) offset
        in
        Builder.logical builder
        @@ AbsPeriodic
             { out
             ; period
             ; error
             ; offset = Option.value ~default:(const Rational.zero) offset
             };
        Ok context
      | CPeriodDrift { period; error; offset } ->
        let period = compile_duration period in
        let* context, error =
          compile_duration_inline_relation ~context ~scope ~builder error
        in
        let* context, offset =
          map_context_opt_result ~context (compile_duration_expr ~scope) offset
        in
        Builder.logical builder
        @@ CumulPeriodic
             { out
             ; period
             ; error
             ; offset = Option.value ~default:(const Rational.zero) offset
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
    then Error (IncorrectValue (location, "incorrect percentage range (0 <= p <= 100)"))
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
      Builder.probab builder @@ DiscreteValued { name = var; ratios };
      Ok (context, var))
  in
  let rec compile_stmt ~context ~scope ~builder stmt =
    match Loc.unwrap stmt with
    | VariableDeclaration list ->
      List.fold_left
        (fun (context, errors) (vars, expected_type) ->
           List.fold_left
             (fun (context, errors) var ->
                Context.add_variable
                  ~context
                  ~prefix:scope
                  (Loc.unwrap var)
                  expected_type
                  (Loc.where var)
                |> Result.map fst
                |> error_recover ~context ~errors)
             (context, errors)
             vars)
        (context, [])
        list
    | DurationRelation (left_ast, rights) ->
      error_recover
        ~context
        ~errors:[]
        (let* context, left = compile_duration_expr ~context ~scope left_ast in
         let* context, _, _ =
           List.fold_left
             (fun state (comp, right_ast) ->
                let* context, left, left_ast = state in
                let* context, right = compile_duration_expr ~context ~scope right_ast in
                let* _ =
                  match left, right with
                  | Const cl, Const cr ->
                    if Expr.do_rel ~compare:Number.Rational.compare comp cl cr
                    then Ok ()
                    else
                      Error (IncorrectComparison (Loc.repack [ left_ast; right_ast ]).loc)
                  | Const cl, Var v ->
                    Builder.duration builder (NumRelation (v, Expr.flip comp, Const cl));
                    Ok ()
                  | Var v, x ->
                    Builder.duration builder (NumRelation (v, comp, x));
                    Ok ()
                in
                Ok (context, right, right_ast))
             (Ok (context, left, left_ast))
             rights
         in
         Ok context)
    | IntRelation (left_ast, rights) ->
      error_recover
        ~context
        ~errors:[]
        (let* context, left = compile_int_expr ~context ~scope left_ast in
         let* context, _, _ =
           List.fold_left
             (fun state (comp, right_ast) ->
                let* context, left, left_ast = state in
                let* context, right = compile_int_expr ~context ~scope right_ast in
                let* _ =
                  match left, right with
                  | Const cl, Const cr ->
                    if Expr.do_rel ~compare:Int.compare comp cl cr
                    then Ok ()
                    else
                      Error (IncorrectComparison (Loc.repack [ left_ast; right_ast ]).loc)
                  | Const cl, Var v ->
                    Builder.integer builder (NumRelation (v, Expr.flip comp, Const cl));
                    Ok ()
                  | Var v, x ->
                    Builder.integer builder (NumRelation (v, comp, x));
                    Ok ()
                in
                Ok (context, right, right_ast))
             (Ok (context, left, left_ast))
             rights
         in
         Ok context)
    | ClockRelation (left, comp, right) ->
      error_recover
        ~context
        ~errors:[]
        (let* context, left =
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
           | Coincidence ->
             if left = right then None else Some (Coincidence [ left; right ])
           | Exclusion ->
             Some (Exclusion { args = [ left; right ]; choice = None })
             (* TODO: add exclusion with variable *)
           | Precedence -> Some (Precedence { cause = left; conseq = right })
           | Causality -> Some (Causality { cause = left; conseq = right })
           | Subclocking _ ->
             Some (Subclocking { sub = left; super = right; choice = percent_var })
           | Alternation strict ->
             Some (Alternate { first = left; second = right; strict })
         in
         Option.iter (Builder.logical builder) constr;
         Ok context)
    | DiscreteValued { var; values; ratios } ->
      error_recover
        ~context
        ~errors:[]
        (let values = Loc.unwrap values
         and ratios = Loc.unwrap ratios in
         let* context, name = Context.resolve ~context ~scope ~expect:`Int var in
         Builder.probab builder
         @@ DiscreteValued { name; ratios = List.combine values ratios };
         Ok context)
    | ContinuousValued { var; dist } ->
      error_recover
        ~context
        ~errors:[]
        (let* context, name = Context.resolve ~context ~scope ~expect:`Duration var in
         Builder.probab builder
         @@ ContinuousValued { name; dist = compile_distribution (Loc.unwrap dist) };
         Ok context)
    | Pool (n, pairs) ->
      (*TODO: make it mutex only *)
      error_recover
        ~context
        ~errors:[]
        (let alloc, dealloc = List.split pairs in
         let* context, alloc = compile_clock_exprs ~context ~scope ~builder alloc in
         let* context, dealloc = compile_clock_exprs ~context ~scope ~builder dealloc in
         let pairs = List.combine alloc dealloc in
         Builder.logical builder @@ Pool (n, pairs);
         Ok context)
    | Block { name; statements } ->
      compile_block
        ~scope:(List.append scope [ Loc.unwrap name ])
        ~context
        ~builder
        statements
    | Allow { clocks; left; right } ->
      error_recover
        ~context
        ~errors:[]
        (let* context, clocks = compile_clock_exprs ~context ~scope ~builder clocks in
         let* context, left =
           compile_clock_expr ~context ~scope ~builder ~result_variable:None left
         in
         let* context, right =
           compile_clock_expr ~context ~scope ~builder ~result_variable:None right
         in
         Builder.logical builder @@ Allow { args = clocks; left; right };
         Ok context)
    | Forbid { clocks; left; right } ->
      error_recover
        ~context
        ~errors:[]
        (let* context, clocks = compile_clock_exprs ~context ~scope ~builder clocks in
         let* context, left =
           compile_clock_expr ~context ~scope ~builder ~result_variable:None left
         in
         let* context, right =
           compile_clock_expr ~context ~scope ~builder ~result_variable:None right
         in
         Builder.logical builder @@ Forbid { args = clocks; left; right };
         Ok context)
    | AdditiveUnion (v, u, e) ->
      error_recover
        ~context
        ~errors:[]
        (let* context, v = Context.resolve_local ~context ~scope ~expect:`Clock v in
         let* context, e =
           compile_clock_expr ~context ~scope ~builder ~result_variable:None e
         in
         Ok (Context.additive_constraint ~context v u e))
  and compile_block ~scope ~context ~builder stmts =
    List.fold_left
      (fun (context, errors) v ->
         accumulate_errors ~errors @@ compile_stmt ~context ~scope ~builder v)
      (context, [])
      stmts
  in
  let compile_top_block name stmts (context, errors) builder =
    let context = Context.next_root context name in
    let context, errors =
      accumulate_errors ~errors @@ compile_block ~scope:[] ~context ~builder stmts
    in
    Context.extract_additive_constraints context builder;
    context, errors
  in
  let compile_top_blocks name list =
    List.mapi
      (fun i ->
         let name = Printf.sprintf "%s%d" name i in
         compile_top_block name)
      list
  in
  let context = Context.empty in
  let (context, errors), m =
    Mrtccsl.Language.Module.make_stateful
      (compile_top_blocks "assume" assumptions)
      (compile_top_block "structure" structure)
      (compile_top_blocks "assert" assertions)
      (context, [])
  in
  let context, errors = finilize_errors (context, errors) in
  context, m, errors
;;

let finilize_errors (context, errors) = context, List.rev errors
