{
  open Parser

  let parse_prefix = function
  | 'm' -> 1, 1_000
  | 'u' -> 1, 1_000_000
  | 'n' -> 1, 1_000_000_000
  | 'p' -> 1, 1_000_000_000_000
  | 'k' -> 1_000, 1
  | 'M' -> 1_000_000, 1
  | 'G' -> 1_000_000_000, 1
  | 'T' -> 1_000_000_000_000, 1
  | s -> failwith (Printf.sprintf "unknown SI prefix: %c" s)
}

let white = [' ' '\t']+
let digit = ['0'-'9']
let int = '-'? digit+
let dec = int '.' digit+
let letter = ['a'-'z' 'A'-'Z']
let id = ('_' | letter) ('_'|letter|digit)*

rule read =
  parse
  | "\n" { MenhirLib.LexerUtil.newline lexbuf; read lexbuf }
  | white { read lexbuf }
  | "//" { single_comment (Buffer.create 16) lexbuf }  (* TODO: redo the comments, I want to make formatter too. *)
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LBRACKET }
  | "]" { RBRACKET }
  | ',' { COMMA }
  | "=" { COINCIDENCE }
  | "==" { EQUAL }  
  | "!=" { NOTEQUAL }  
  | ";" { SEMICOLON }
  | "." { DOT }
  | "$" { DOLLAR }
  | ":" { COLON }
  | "+" { PLUS }
  | "-" { MINUS }
  | "+-" { PLUSMINUS }
  | "*" { STAR }
  | "/" { SLASH }
  | "<" { LESS }
  | "<=" { LESSEQ }
  | ">" { MORE }
  | ">=" { MOREEQ }
  | "->" { ARROWRIGHT }
  | "?" { QUESTION }
  | "@" { AT }
  | "#" { SHARP }
  | "%" { PERCENT }
  | ":=" { COLONEQ }
  (* keywords *)
  | "allow" { ALLOW }
  | "forbid" { FORBID }
  | "in" { IN }
  | "next" { NEXT }
  | "fastest" { FASTEST }
  | "slowest" { SLOWEST }
  | "assume" { ASSUME }
  | "assert" { ASSERT }
  | "sample" { SAMPLE }
  | "on" { ON }
  | "alternates" { ALTERNATES }
  | "delay" { DELAY }
  | "interface" { INTERFACE }
  | "upper" { UPPER }
  | "lower" { LOWER }
  | "where" { WHERE }
  | "and" { AND }
  | "or" { OR }
  | "xor" { XOR }
  | "by" { BY }
  | "is" { IS }
  | "skip" { SKIP }
  | "every" { EVERY }
  | "of" { OF }
  | "find" { FIND }
  | "mod" { MOD }
  | "periodic" { PERIODIC }
  | "rel.error" { RELATIVE_ERROR }
  | "abs.error" { ABSOLUTE_ERROR }
  | "offset" { OFFSET }
  | "mutex" { MUTEX }
  | "pool" { POOL }
  | "method" { METHOD }
  | "sporadic" { SPORADIC }
  | "non-strict" { STRICT(false) }
  | "strict" { STRICT(true) }
  | "subclocks" { SUBCLOCKS }
  | "first-sampled" { FIRSTSAMPLED }
  | "last-sampled" { LASTSAMPLED }
  | "causes" {CAUSES}
  | "precedes" {PRECEDES}
  | "except" {EXCEPT}
  | "when" {WHEN}
  (* time scales and units *)
  | "year" { SECOND(365*24*60*60, 1) }
  | "month" { SECOND(30*24*60*60, 1) }
  | "week" {SECOND(7*24*60*60, 1)}
  | "day" { SECOND(24*60*60, 1) }
  | "hour" { SECOND(60*60, 1) }
  | "min" { SECOND(60, 1) }
  | "s" { SECOND(1, 1) }
  | "Hz" { HERTZ(1, 1) }
  | ("m" | "u" | "n"| "p"| "k"| "M" | "G" | "T" as prefix) "s" { let nom,denom = parse_prefix prefix in SECOND(nom,denom) }
  | ("m" | "u" | "n"| "p"| "k"| "M" | "G" | "T" as prefix) "Hz" { let nom,denom = parse_prefix prefix in HERTZ(nom,denom) }
  | "ppm" {PPM}
   (* types *)
  | "integer" {TYPE_INT }
  | "rational" {TYPE_RATIONAL}
  | "interval" {TYPE_INTERVAL}
  | "frequency" {TYPE_FREQUENCY}
  | "time" {TYPE_TIME}
  | "clock" {TYPE_CLOCK}
  | "block" {TYPE_BLOCK}
  (* Properties *)
  | "schedulable" {SCHEDULABLE}
  | "live" {LIVE(false)}
  | "weak live" {LIVE(true)}
  | "safe" {FINITENESS}
  | "finite" {FINITENESS}
  | "exists" {EXISTS}
  (* Else *)
  | id { ID (Lexing.lexeme lexbuf) }
  | int { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | dec { DECIMAL (Number.Rational.of_decimal_string (Lexing.lexeme lexbuf)) }
  | eof { EOF }
  | _ { print_endline "lexer error"; print_endline (Lexing.lexeme lexbuf);
        exit 2 }
and id =
  parse 
  | id { ID (Lexing.lexeme lexbuf) }
  | _ {failwith "cannot parse as ID"}
and single_comment buf =
  parse
  | "\n" {  MenhirLib.LexerUtil.newline lexbuf;read lexbuf }
  | _ { single_comment buf lexbuf }
