%{
    open Prelude
    open Ast
%}

%token <int> INT
%token <string> ID
%token <Rational.t> DECIMAL
%token DOT
%token LBRACE RBRACE LPAREN RPAREN LBRACKET RBRACKET (* brackets *)
%token COMMA COLON SEMICOLON (* delimiters *)
%token TYPE_INT TYPE_RATIONAL TYPE_TIME TYPE_CLOCK TYPE_FREQUENCY TYPE_INTERVAL TYPE_BLOCK (* types *)
%token SCHEDULABLE FINITENESS EXISTS IS FIND WHERE (*properties*)
%token <int * int> SECOND HERTZ
%token <bool> LIVE
%token MOD ASSUME ASSERT UPPER LOWER INTERFACE METHOD (*modules*)
%token AT IN QUESTION COLONEQ (* special syntax inside modules *)
%token ARROWRIGHT ALLOW FORBID NEXT FASTEST SLOWEST DOLLAR SAMPLE ON ALTERNATES DELAY BY SKIP EVERY PERIODIC RELATIVE_ERROR ABSOLUTE_ERROR OFFSET MUTEX POOL SUBCLOCKS SPORADIC FIRSTSAMPLED LASTSAMPLED AND OR XOR COINCIDENCE PRECEDES CAUSES SHARP EXCEPT WHEN (*constraints*)
%left OR
%left XOR
%left AND
%token <bool> STRICT
%token LESS LESSEQ MORE MOREEQ EQUAL NOTEQUAL  (* variable relations *)
 (*expressions *)
%token PLUS MINUS STAR SLASH FLOOR CEIL OF PERCENT PLUSMINUS PPM
%left PLUS MINUS        /* lowest precedence */
%left STAR SLASH         /* medium precedence */
%left SECOND HERTZ 
%nonassoc UMINUS        /* highest precedence */

%token EOF

%type <Ast.file> file
%start file

%%

file : 
| t=toplevel* ; EOF { t }

toplevel :
| params=loption(FIND ; l=separated_list(COMMA, id) ; WHERE {l}) ; stat=statement ; properties=loption(IS ; l=separated_nonempty_list(AND, property) {l}); SEMICOLON { Check {params;stat;properties} }
| MOD ; name=id ; args=delimited(LPAREN, separated_list(COMMA,argument_dec),RPAREN) ; 
  assumption=opt_mod_block(ASSUME) ;
  structure=delimited(LBRACE, statements, RBRACE) ; 
  assertion=opt_mod_block(ASSERT) ;
  upper_interface=opt_mod_block(UPPER ; INTERFACE {});
  lower_interface=opt_mod_block(LOWER ; INTERFACE {})
  { ModuleDec{name; args;assumption;structure;assertion;upper_interface;lower_interface} }

%inline opt_mod_block (NAME) : r=loption(preceded(NAME, delimited(LBRACE, statements, RBRACE))) {r}

argument_dec : arg=id ; COLON ; t=type_name { (arg,t) }

type_name :
| TYPE_INT { `Int }
| TYPE_RATIONAL { `Rational }
| TYPE_TIME {`Time}
| TYPE_FREQUENCY { `Frequency }
| TYPE_INTERVAL ; LESS ; inner=type_name ; MORE { `Interval inner}
| TYPE_CLOCK { `Clock }
| TYPE_BLOCK { `Block }

property :
| SCHEDULABLE {Schedulability}
| FINITENESS {Finiteness}
| weak=LIVE ; clocks=loption(delimited(LPAREN,separated_list(COMMA, path),RPAREN)) { Liveness {exists=false; weak; clocks}}
| EXISTS ; weak=LIVE ; clocks=loption(delimited(LPAREN,separated_list(COMMA, path),RPAREN)) { Liveness {exists=true; weak; clocks}}

statements :
| l=separated_list(SEMICOLON, option(statement)) {let l,_ = List.flatten_opt l in l }
statement : statement0 {Loc.make $symbolstartpos $endpos $1}
%inline statement0 : 
| e=num_expr ; l=pair(num_rel,num_expr)+ {NumRelation (e,l)}
| e=clock_expr ; l=pair(clock_rel,clock_expr)+ {ClockRelation (e,l)}
| e1=clock_expr ; rel=exn_rel ; e2=clock_expr {ExtensibleRelation (e1,rel,e2)}
| arg=num_expr ; IN ; bounds=interval_expr {IntervalRelation { arg; bounds}}
| b1=block_expr ; COLONEQ ; b2=block_expr {BlockEquivalence (b1, b2)}
| METHOD ; name=id ; args=delimited(LPAREN, separated_list(COMMA,argument_dec),RPAREN) ; body=delimited(LBRACE, statements, RBRACE){Method {name;args;body}}
| ALLOW ; clocks=separated_list(COMMA, clock_expr); IN ; inside=interval(clock_expr) { Allow {clocks;inside} }
| FORBID ; clocks=separated_list(COMMA, clock_expr); IN ; inside=interval(clock_expr) { Forbid {clocks;inside} }

%inline exn_rel : 
| OR ; COINCIDENCE { OrCoincidence }
| OR ; PRECEDES { OrPrecedence }
| OR ; CAUSES { OrCausality }
| XOR ; COINCIDENCE { XorCoincidence }
| XOR ; PRECEDES { XorPrecedence }
| XOR ; CAUSES { XorCausality }

interval_expr : interval_expr0 {Loc.make $symbolstartpos $endpos $1}
interval_expr0 :
| LPAREN ; e=interval_expr0 ; RPAREN {e}
| v=variable_expr {Variable v}
| i=interval(num_expr) {Interval i}
| i=interval_expr ; r=binop ; e=num_expr {LeftBinOp (i,r,e)}
| e=num_expr; r=binop ; i=interval_expr {RightBinOp (e,r,i)}
| num_expr {Singleton $1}
| MINUS ; e=interval_expr %prec UMINUS { NegInterval(e) }
| PLUSMINUS ; frac=num_const ; PERCENT ; OF; freq=num_expr { let wrap x = Loc.make $symbolstartpos $endpos x in let error = wrap (BinOp (wrap (BinOp (wrap (RationalConstant (Rational.from_pair 1 100)), Mul, (Loc.make $startpos(frac) $endpos(frac) frac))), Mul, freq)) in (Interval {left_strict=false;right_strict=false;left=wrap (UnOp (Neg, error)); right=error}) }
| ppm=num_const ; PPM ; OF ; freq=num_expr {  let wrap x = Loc.make $symbolstartpos $endpos x in let error = wrap (BinOp (wrap (BinOp (wrap (RationalConstant (Rational.from_pair 1 1_000_000)), Mul, (Loc.make $startpos(ppm) $endpos(ppm) ppm))), Mul, freq)) in (Interval {left_strict=false;right_strict=false;left=wrap (UnOp (Neg, error)); right=error})  }

%inline interval (X) : 
| left_strict=left_bound ; left=X ; COMMA ; right=X ; right_strict=right_bound {{left_strict; left; right; right_strict}}

%inline left_bound : LPAREN {true} | LBRACKET {false}
%inline right_bound : RPAREN {true} | RBRACKET {false}
%inline num_const : 
| i=INT { IntConstant i }
| r=DECIMAL {RationalConstant r}

variable_expr : scope=count(AT) ; id=separated_nonempty_list(DOT, name_expr) {Dereference {id; scope}}
name_expr: 
| var=id {Identifier var}
| id=id ; LPAREN ; args=separated_list(COMMA, expr) ; RPAREN { ModCall {id;args}}

expr : 
| variable_expr {WildcardVariable $1}
| num_expr {NumExpr $1}
| clock_expr {ClockExpr $1 }
| interval_expr {NumIntervalExpr $1 }
| interval(expr) {IntervalExpr $1 }
| block_expr { BlockExpr $1 }

clock_expr : clock_expr0 {Loc.make $symbolstartpos $endpos $1}
clock_expr0 :
| LPAREN ; e=clock_expr0 ; RPAREN {e}
| v=variable_expr {Variable v}
| arg=clock_expr ; DOLLAR ; delay=interval_expr ; on=option(ON ; e=clock_expr {e}) { Delay {arg;delay;on} }
| skip=option(SKIP ; e=num_expr {e}) ; EVERY ; period=num_expr ; base=clock_expr { Periodic {skip=(Option.value ~default:(Loc.nowhere (IntConstant 0)) skip);period;base}}
| NEXT ; arg=clock_expr {Delay {arg;delay=Loc.nowhere (Singleton (Loc.nowhere (IntConstant 1))); on=None}}
| SAMPLE ; arg=clock_expr ; ON ; base=clock_expr { Sample{arg;base} }
| FASTEST ; LPAREN ; clocks=separated_list(COMMA, clock_expr) ; RPAREN { Fastest clocks }
| SLOWEST ; LPAREN ; clocks=separated_list(COMMA, clock_expr) ; RPAREN { Slowest clocks }
| FIRSTSAMPLED ; arg=clock_expr ; ON ; base=clock_expr {FirstSampled {arg;base}}
| LASTSAMPLED ; arg=clock_expr ; ON ; base=clock_expr {FirstSampled {arg;base}}
| left=clock_expr ; AND ; right=clock_expr { Intersection {left;right}}
| left=clock_expr ; XOR ; right=clock_expr { Union {left;right}}
| left=clock_expr ; OR ; right=clock_expr { DisjUnion {left;right}}
| left=clock_expr ; EXCEPT ; WHEN ; right=clock_expr { Minus {left;right}}
| DELAY ; arg=clock_expr ; BY ; delay=interval_expr {RTDelay {arg;delay}}
| PERIODIC ; period=num_expr ; RELATIVE_ERROR ; error=interval_expr ; offset=option(preceded(OFFSET, interval_expr)) { CumulPeriodic {period;error;offset}}
| PERIODIC ; period=num_expr ; ABSOLUTE_ERROR ; error=interval_expr ; offset=option(preceded(OFFSET, interval_expr)) { AbsPeriodic {period;error;offset}}
| at_least=num_expr ; strict=STRICT SPORADIC {Sporadic {at_least; strict}} 

num_expr : num_expr0 {Loc.make $symbolstartpos $endpos $1}
num_expr0 :
| v=variable_expr {Variable v}
| LPAREN ; e=num_expr0 ; RPAREN {e}
| num_const {$1}
| e1=num_expr ; r=binop ; e2=num_expr {BinOp(e1,r,e2)} 
| r=unop ; LPAREN ; e=num_expr ; RPAREN {UnOp(r,e)} 
| MINUS ; e=num_expr %prec UMINUS { UnOp(Neg, e) }
| e=num_expr ; unit=si_unit { let (nom,denom,typ) = unit in SIUnit {expr=e; scale=Rational.from_pair nom denom; into=typ}}
| QUESTION {Hole} 

block_expr : block_expr0 {Loc.make $symbolstartpos $endpos $1}
%inline block_expr0 :
| v=variable_expr {Variable v}
| delimited(LBRACE, statements, RBRACE) {Block $1}
| MUTEX ; alloc_delloc=delimited(LBRACE, dangling_list(COMMA, separated_pair(expr, ARROWRIGHT, expr)), RBRACE) { (Mutex (alloc_delloc))}
| POOL ; LPAREN ; n=INT; LBRACE; alloc_delloc=dangling_list(COMMA, separated_pair(expr, ARROWRIGHT, expr)); RBRACE; RPAREN { (Pool (n, alloc_delloc))}

%inline si_unit : 
| v=SECOND {let (nom,denom) = v in (nom,denom,`Time)}
| v=HERTZ {let (nom,denom) = v in (nom,denom,`Frequency)}

%inline unop :
| FLOOR {Floor}
| CEIL {Ceil}

%inline binop :
| PLUS {Add}
| MINUS {Sub}
| STAR {Mul}
| SLASH {Div}

%inline num_rel :
| LESS {Less}
| LESSEQ {LessEq}
| EQUAL {Eq}
| MORE {More}
| MOREEQ {MoreEq}
| NOTEQUAL {Neq}

%inline clock_rel:
| COINCIDENCE {Coincidence}
| SHARP {Exclusion}
| ALTERNATES {Alternation}
| SUBCLOCKS {Subclocking}
| PRECEDES {Precedence}
| CAUSES {Causality}

path : path=separated_nonempty_list(DOT, id) { path }

count(X): {0} | X ; next=count(X) { next+1 }

dangling_list(sep, X):
| l=loption(non_empty_dangling_list(sep, X)) {l}

non_empty_dangling_list(sep, X):
| x=X ; sep? { [x] }
| x=X ; sep ; tail=non_empty_dangling_list(sep, X) { x::tail } 

%inline id : id=ID {Loc.make $symbolstartpos $endpos id}