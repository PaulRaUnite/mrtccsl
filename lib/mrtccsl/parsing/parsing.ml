open Prelude

let shift_position (p : Lexing.position) offset =
  let open Lexing in
  let { pos_cnum; pos_bol; _ } = p in
  { p with pos_cnum = pos_cnum + offset; pos_bol = pos_bol + offset }
;;

let highlight warning lexbuf (s : Lexing.position) (f : Lexing.position) (msg : string) =
  if not (String.equal s.pos_fname f.pos_fname)
  then failwith "Trying to highlight range in different files"
  else (
    let reset_ppf = Spectrum.prepare_ppf Format.std_formatter in
    if s.pos_lnum = f.pos_lnum
    then (
      (* Format.printf "start=%i finish=%i %i %i\n" s.pos_cnum f.pos_cnum s.pos_bol (Bytes.length lexbuf); *)
      let prefix = Bytes.sub lexbuf s.pos_bol (s.pos_cnum - s.pos_bol) in
      let offset =
        Bytes.fold_right
          (fun c mono ->
            mono
            +
            match c with
            | '\t' -> 4
            | _ -> 1)
          prefix
          0
      and width = max (f.pos_cnum - s.pos_cnum) 1
      and linenum = Format.sprintf "%i | " s.pos_lnum
      and linewidth =
        Fun.catch_with_default
          (Bytes.index_from lexbuf f.pos_cnum)
          '\n'
          (Bytes.length lexbuf)
        - s.pos_bol
      in
      Format.print_string linenum;
      Format.print_string
        (String.replace
           ~sub:"\t"
           ~by:"    "
           (Bytes.sub_string lexbuf s.pos_bol linewidth));
      Format.print_newline ();
      for _ = 0 to String.length linenum + offset - 1 do
        Format.print_char ' '
      done;
      let buf = Buffer.create 16 in
      Buffer.add_chars buf width '^';
      Buffer.add_char buf '\n';
      Buffer.add_string buf (if warning then "Warning: " else "Error: ");
      Buffer.add_string buf msg;
      if warning
      then Format.printf "@{<yellow>%s@}\n" (Buffer.contents buf)
      else Format.printf "@{<red>%s@}\n" (Buffer.contents buf);
      print_endline "")
    else ();
    reset_ppf ())
;;

let string_token =
  let open Parser in
  function
  | WHERE -> "WHERE"
  | UPPER -> "UPPER"
  | TYPE_TIME -> "TYPE_TIME"
  | TYPE_RATIONAL -> "TYPE_RATIONAL"
  | TYPE_INTERVAL -> "TYPE_INTERVAL"
  | TYPE_INT -> "TYPE_INT"
  | TYPE_FREQUENCY -> "TYPE_FREQUENCY"
  | TYPE_CLOCK -> "TYPE_CLOCK"
  | TYPE_BLOCK -> "TYPE_BLOCK"
  | STAR -> "STAR"
  | SLOWEST -> "SLOWEST"
  | SLASH -> "SLASH"
  | SKIP -> "SKIP"
  | SHARP -> "SHARP"
  | SEMICOLON -> "SEMICOLON"
  | SECOND (nom, denom) -> Printf.sprintf "SECOND(%i,%i)" nom denom
  | SCHEDULABLE -> "SCHEDULABLE"
  | SAMPLE -> "SAMPLE"
  | RPAREN -> "RPAREN"
  | RBRACKET -> "RBRACKET"
  | RBRACE -> "RBRACE"
  | QUESTION -> "QUESTION"
  | PLUS -> "PLUS"
  | ON -> "ON"
  | OF -> "OF"
  | NEXT -> "NEXT"
  | MOREEQ -> "MOREEQ"
  | MORE -> "MORE"
  | MOD -> "MOD"
  | MINUS -> "MINUS"
  | LPAREN -> "LPAREN"
  | LOWER -> "LOWER"
  | LIVE weak -> if weak then "LIVE(true)" else "LIVE(false)"
  | LESSEQ -> "LESSEQ"
  | LESS -> "LESS"
  | LBRACKET -> "LBRACKET"
  | LBRACE -> "LBRACE"
  | IS -> "IS"
  | INTERFACE -> "INTERFACE"
  | INT i -> Printf.sprintf "INT(%i)" i
  | IN -> "IN"
  | ID s -> Printf.sprintf "ID(%s)" s
  | HERTZ (nom, denom) -> Printf.sprintf "HERTZ(%i,%i)" nom denom
  | FORBID -> "FORBID"
  | FLOOR -> "FLOOR"
  | FINITENESS -> "FINITENESS"
  | FIND -> "FIND"
  | FASTEST -> "FASTEST"
  | EXISTS -> "EXISTS"
  | EVERY -> "EVERY"
  | EQUAL -> "EQUAL"
  | EOF -> "EOF"
  | DOT -> "DOT"
  | DOLLAR -> "DOLLAR"
  | DELAY -> "DELAY"
  | DECIMAL n -> Printf.sprintf "DECIMAL(%s)" (Number.Rational.to_string n)
  | COMMA -> "COMMA"
  | COLON -> "COLON"
  | CEIL -> "CEIL"
  | BY -> "BY"
  | AT -> "AT"
  | ASSUME -> "ASSUME"
  | ASSERT -> "ASSERT"
  | ARROWRIGHT -> "ARROWRIGHT"
  | AND -> "AND"
  | ALTERNATES -> "ALTERNATES"
  | ALLOW -> "ALLOW"
  | PPM -> "PPM"
  | PLUSMINUS -> "PLUSMINUS"
  | PERCENT -> "PERCENT"
  | RELATIVE_ERROR -> "RELATIVE_ERROR"
  | ABSOLUTE_ERROR -> "ABSOLUTE_ERROR"
  | PERIODIC -> "PERIODIC"
  | OFFSET -> "OFFSET"
  | METHOD -> "METHOD"
  | POOL -> "POOL"
  | MUTEX -> "MUTEX"
  | SUBCLOCKS -> "SUBCLOCKS"
  | SPORADIC -> "SPORADIC"
  | FIRSTSAMPLED -> "FIRSTSAMPLED"
  | LASTSAMPLED -> "LASTSAMPLED"
  | STRICT v -> Printf.sprintf "STRICT(%b)" v
  | PRECEDES -> "PRECEDES"
  | CAUSES -> "CAUSES"
  | OR -> "OR"
  | XOR -> "XOR"
  | NOTEQUAL -> "NOTEQUAL"
  | COLONEQ -> "COLONEQ"
  | COINCIDENCE -> "COINCIDENCE"
  | EXCEPT -> "EXCEPT"
  | WHEN -> "WHEN"
;;

let print_tokens l =
  List.iter (fun (_, t, _, _) -> Printf.printf "%s " (string_token t)) l;
  print_endline ""
;;

type 'a control =
  | Ready of Ast.file
  | Failed
  | Retry of Ast.file Parser.MenhirInterpreter.checkpoint * 'a

let prefix_supply prefix supplier =
  let prefixed = ref false in
  let supply () =
    if !prefixed
    then supplier ()
    else (
      prefixed := true;
      prefix)
  in
  supply
;;

let retrying = function
  | Retry _ -> true
  | _ -> false
;;

let parse_with_error_handling buffer =
  let last_tokens = CircularList.make 10 in
  let supply = Parser.MenhirInterpreter.lexer_lexbuf_to_supplier Lexer.read buffer in
  let supply () =
    let token, startp, endp = supply () in
    CircularList.push last_tokens (Lexing.lexeme buffer, token, startp, endp);
    token, startp, endp
  in
  let checkpoint = Parser.Incremental.file buffer.lex_curr_p in
  let rec drive supply checkpoint =
    let result =
      Parser.MenhirInterpreter.loop_handle_undo
        (fun ast -> Ready ast)
        (fun input _conseq ->
          let next_action =
            match List.last (CircularList.content last_tokens) with
            | Some (lexeme, _, startp, endp) ->
              (match Fun.catch_to_opt Lexer.id (Lexing.from_string lexeme) with
               | Some token ->
                 if Parser.MenhirInterpreter.acceptable input token startp
                 then Retry (input, (token, startp, endp))
                 else Failed
               | _ -> Failed)
            | None -> Failed
          in
          let range = MenhirLib.LexerUtil.range (buffer.lex_start_p, buffer.lex_curr_p) in
          print_string range;
          let _ =
            if retrying next_action
            then
              highlight
                true
                buffer.lex_buffer
                buffer.lex_start_p
                buffer.lex_curr_p
                "Unexpected token, but recovered by interpretting as identifier"
            else (
              highlight
                false
                buffer.lex_buffer
                buffer.lex_start_p
                buffer.lex_curr_p
                "Unexpected token, cannot recover";
              print_tokens (CircularList.content last_tokens))
          in
          next_action)
        supply
        checkpoint
    in
    match result with
    | Retry (checkpoint, new_token) -> drive (prefix_supply new_token supply) checkpoint
    | x -> x
  in
  drive supply checkpoint
;;

let from_file path =
  let _, buffer = MenhirLib.LexerUtil.read path in
  parse_with_error_handling buffer
;;

let from_string s =
  let buffer = Lexing.from_string ~with_positions:true s in
  parse_with_error_handling buffer
;;
