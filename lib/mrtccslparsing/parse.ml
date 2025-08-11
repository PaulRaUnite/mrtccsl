open Prelude

let string_token =
  let open Parser in
  function
  | STAR -> "STAR"
  | SLOWEST -> "SLOWEST"
  | SLASH -> "SLASH"
  | SKIP -> "SKIP"
  | SHARP -> "SHARP"
  | SEMICOLON -> "SEMICOLON"
  | SECOND (nom, denom) -> Printf.sprintf "SECOND(%i,%i)" nom denom
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
  | MINUS -> "MINUS"
  | LPAREN -> "LPAREN"
  | LESSEQ -> "LESSEQ"
  | LESS -> "LESS"
  | LBRACKET -> "LBRACKET"
  | LBRACE -> "LBRACE"
  | INT i -> Printf.sprintf "INT(%i)" i
  | ID s -> Printf.sprintf "ID(%s)" s
  | HERTZ (nom, denom) -> Printf.sprintf "HERTZ(%i,%i)" nom denom
  | FASTEST -> "FASTEST"
  | EVERY -> "EVERY"
  | EQUAL -> "EQUAL"
  | EOF -> "EOF"
  | DOT -> "DOT"
  | DOLLAR -> "DOLLAR"
  | DELAY -> "DELAY"
  | DECIMAL n -> Printf.sprintf "DECIMAL(%s)" (Number.Rational.to_string n)
  | COMMA -> "COMMA"
  | COLON -> "COLON"
  | BY -> "BY"
  | AT -> "AT"
  | ASSUME -> "ASSUME"
  | ASSERT -> "ASSERT"
  | ARROWRIGHT -> "ARROWRIGHT"
  | AND -> "AND"
  | ALTERNATES -> "ALTERNATES"
  | PPM -> "PPM"
  | PLUSMINUS -> "PLUSMINUS"
  | PERCENT -> "PERCENT"
  | PERIODIC -> "PERIODIC"
  | OFFSET -> "OFFSET"
  | POOL -> "POOL"
  | MUTEX -> "MUTEX"
  | SUBCLOCKS -> "SUBCLOCKS"
  | SPORADIC -> "SPORADIC"
  | STRICT -> "STRICT"
  | PRECEDES -> "PRECEDES"
  | CAUSES -> "CAUSES"
  | OR -> "OR"
  | XOR -> "XOR"
  | NOTEQUAL -> "NOTEQUAL"
  | COINCIDENCE -> "COINCIDENCE"
  | EXCEPT -> "EXCEPT"
  | WITH -> "WITH"
  | UNIFORM -> "UNIFORM"
  | STRUCTURE -> "STRUCTURE"
  | SIM -> "SIM"
  | PROCESS -> "PROCESS"
  | NORMAL -> "NORMAL"
  | JITTER -> "JITTER"
  | INTEGER -> "INTEGER"
  | DURATION -> "DURATION"
  | DRIFT -> "DRIFT"
  | DISCRETE -> "DISCRETE"
  | CONTINUOUS -> "CONTINUOUS"
  | CLOCK -> "CLOCK"
  | VAR -> "VAR"
;;

let test_tokens =
  Parser.
    [ XOR
    ; WITH
    ; VAR
    ; UNIFORM
    ; SUBCLOCKS
    ; STRUCTURE
    ; STRICT
    ; STAR
    ; SPORADIC
    ; SLOWEST
    ; SLASH
    ; SKIP
    ; SIM
    ; SHARP
    ; SEMICOLON
    ; SECOND (1, 1)
    ; SAMPLE
    ; RPAREN
    ; RBRACKET
    ; RBRACE
    ; QUESTION
    ; PROCESS
    ; PRECEDES
    ; PPM
    ; POOL
    ; PLUSMINUS
    ; PLUS
    ; PERIODIC
    ; PERCENT
    ; OR
    ; ON
    ; OFFSET
    ; OF
    ; NOTEQUAL
    ; NORMAL
    ; NEXT
    ; MUTEX
    ; MOREEQ
    ; MORE
    ; MINUS
    ; LPAREN
    ; LESSEQ
    ; LESS
    ; LBRACKET
    ; LBRACE
    ; JITTER
    ; INTEGER
    ; INT 0
    ; ID "test"
    ; HERTZ (1, 1)
    ; FASTEST
    ; EXCEPT
    ; EVERY
    ; EQUAL
    ; EOF
    ; DURATION
    ; DRIFT
    ; DOT
    ; DOLLAR
    ; DISCRETE
    ; DELAY
    ; DECIMAL Number.Rational.zero
    ; CONTINUOUS
    ; COMMA
    ; COLON
    ; COINCIDENCE
    ; CLOCK
    ; CAUSES
    ; BY
    ; AT
    ; ASSUME
    ; ASSERT
    ; ARROWRIGHT
    ; AND
    ; ALTERNATES
    ]
;;

let pp_tokens formatter l =
  Format.pp_print_list
    ~pp_sep:Format.pp_print_space
    (fun f t -> Format.pp_print_string f (string_token t))
    formatter
    l
;;

type 'a control = (Ast.module_body_declaration, 'a) result

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

let parse_with_error_handling buffer =
  let last_tokens = CircularList.make 10 in
  let supply = Parser.MenhirInterpreter.lexer_lexbuf_to_supplier Lexer.read buffer in
  let supply () =
    let token, startp, endp = supply () in
    CircularList.push last_tokens (Lexing.lexeme buffer, token, startp, endp);
    token, startp, endp
  in
  let start = Parser.Incremental.top_module buffer.lex_curr_p in
  let result =
    Parser.MenhirInterpreter.loop_handle_undo
      Result.ok
      (fun before _ ->
         let acceptable_tokens =
           List.filter
             (fun token ->
                Parser.MenhirInterpreter.acceptable before token Lexing.dummy_pos)
             test_tokens
         in
         Result.error
         @@ Loc.pp_warning
              buffer.lex_buffer
              buffer.lex_start_p
              buffer.lex_curr_p
              (Format.asprintf
                 "Unexpected token, cannot recover.\nLast tokens: %a\nWould accept: %a"
                 pp_tokens
                 (CircularList.content last_tokens
                  |> List.map (fun (_, token, _, _) -> token))
                 pp_tokens
                 acceptable_tokens))
      supply
      start
  in
  result
;;

let from_file path =
  let _, buffer = MenhirLib.LexerUtil.read path in
  parse_with_error_handling buffer
;;

let from_string s =
  let buffer = Lexing.from_string ~with_positions:true s in
  parse_with_error_handling buffer
;;
