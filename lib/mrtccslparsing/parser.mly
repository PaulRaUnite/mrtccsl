%{
    open Prelude
    open Mrtccsl.Language
    open Ast
%}

%token <int> INT
%token <string> ID
%token <Number.Rational.t> DECIMAL
%token DOT
%token LBRACE RBRACE LPAREN RPAREN LBRACKET RBRACKET (* brackets *)
%token COMMA COLON SEMICOLON (* delimiters *)
%token <int * int> SECOND HERTZ
%token INTEGER DURATION CLOCK
%token ASSUME ASSERT STRUCTURE (*modules*)
%token AT QUESTION (* special syntax inside modules *)
%token VAR (* variable declaration *)
%token ARROWRIGHT NEXT FASTEST SLOWEST DOLLAR SAMPLE ON ALTERNATES DELAY BY SKIP EVERY PERIODIC OFFSET MUTEX POOL SUBCLOCKS SPORADIC AND OR XOR COINCIDENCE PRECEDES CAUSES SHARP EXCEPT WITH JITTER DRIFT STRICT (*constraints*)
%token DISCRETE CONTINUOUS PROCESS NORMAL UNIFORM SIM
%token LESS LESSEQ MORE MOREEQ EQUAL NOTEQUAL  (* variable relations *)
 (*expressions *)
%token PLUS MINUS STAR SLASH OF PERCENT PLUSMINUS PPM
%left PLUS MINUS        /* lowest precedence */
%left STAR SLASH         /* medium precedence */
%nonassoc UMINUS        /* highest precedence */

%token EOF

%type<duration_expr'> delim_duration_expr0
%type<clock_expr'> delim_clock_expr0
%type <Ast.module_body_declaration> top_module
%type <Ast.statements> statements
%type <Ast.statement'> statement0
%start top_module statements statement0

%%

%inline addsub :
| PLUS {`Add} [@name add_single]
| MINUS {`Sub} [@name sub_single]

%inline binop :
| PLUS {`Add} [@name add]
| MINUS {`Sub} [@name sub]
| STAR {`Mul} [@name mul]
| SLASH {`Div} [@name div]

%inline num_rel :
| LESS {`Less} [@name less]
| LESSEQ {`LessEq} [@name lesseq]
| EQUAL {`Eq} [@name equal]
| MORE {`More} [@name more]
| MOREEQ {`MoreEq} [@name moreeq]
| NOTEQUAL {`Neq} [@name notequal]

%inline var_type :
| INTEGER { `Int } [@name int]
| DURATION { `Duration } [@name duration]
| CLOCK { `Clock } [@name clock]

dangling_list(sep, X):
| l=loption(non_empty_dangling_list(sep, X)) {l}

non_empty_dangling_list(sep, X):
| x=X ; sep? { [x] }
| x=X ; sep ; tail=non_empty_dangling_list(sep, X) { x::tail } 

%inline located(X) : X {Loc.make $symbolstartpos $endpos $1}

%inline id : id=ID {Loc.make $symbolstartpos $endpos id}

%inline path : separated_nonempty_list(DOT, ID) { $1 }

%inline var : located(path) { $1 }

%inline percentage : DECIMAL ; PERCENT { Percent $1 }

%inline duration : 
| value=DECIMAL ; scale=SECOND { Second { value ; scale=(Number.Rational.from_pair scale) } }
| value=INT ; scale=SECOND {Second {value=Number.Rational.of_int value; scale=(Number.Rational.from_pair scale)}}

%inline interval(X) :
| LBRACKET ; left=X ; COMMA ; right=X ; RBRACKET { Interval {left_strict=false; left; right; right_strict=false} }
| RBRACKET ; left=X ; COMMA ; right=X ; RBRACKET { Interval {left_strict=true; left; right; right_strict=false} }
| LBRACKET ; left=X ; COMMA ; right=X ; LBRACKET { Interval {left_strict=false; left; right; right_strict=true} }
| RBRACKET ; left=X ; COMMA ; right=X ; LBRACKET { Interval {left_strict=true; left; right; right_strict=true} }
| mean=X ; PLUSMINUS ; error=X { PlusMinus (mean,error) }


%inline clock_rel:
| COINCIDENCE {Coincidence}
| SHARP  {Exclusion }
| ALTERNATES {Alternation}
| SUBCLOCKS ; p=option(delimited(LBRACKET, percentage, RBRACKET)) {Subclocking p}
| PRECEDES {Precedence}
| CAUSES {Causality}

contdist : located(contdist0) {$1}
contdist0 :
| NORMAL ; LPAREN ; mean=duration ; COMMA ; deviation=duration ; RPAREN {Normal {mean; deviation}}
| UNIFORM { Uniform }

duration_expr : duration_expr0 {Loc.make $symbolstartpos $endpos $1}
%inline delim_duration_expr0 : 
| LPAREN ; e=duration_expr0 ; RPAREN {e} 
| var {DVariable $1}
| duration {DConstant $1}
delim_duration_expr : delim_duration_expr0 {Loc.make $symbolstartpos $endpos $1}
duration_expr0 :
| delim_duration_expr0 {$1}
| e1=duration_expr ; r=addsub ; e2=duration_expr {DBinOp(e1,r,e2)} 
| e1=DECIMAL ; STAR ; e2=delim_duration_expr {DScaleOp(e1,e2)} 
| MINUS ; e=delim_duration_expr { DNegation e }
| QUESTION { DHole }

int_expr : int_expr0 {Loc.make $symbolstartpos $endpos $1}
int_expr0 :
| INT {IConstant $1}
| var {IVariable $1}
| e1=int_expr ; r=binop ; e2=int_expr {IBinOp(e1,r,e2)}
| MINUS ; e=int_expr { INegation e }
| QUESTION { IHole }

%inline inline_relation(X) : 
| X { Loc.make $symbolstartpos $endpos @@ InlineExpr $1 }
| interval(X)  { Loc.make $symbolstartpos $endpos @@ InlineInterval $1 }

offset : OFFSET ; duration {$2}
skip : SKIP ; inline_relation(int_expr) {$2}

clock_expr : clock_expr0 {Loc.make $symbolstartpos $endpos $1}
%inline delim_clock_expr0 : 
| LPAREN ; e=clock_expr0 ; RPAREN {e}
| var {CVariable $1}
delim_clock_expr : delim_clock_expr0 {Loc.make $symbolstartpos $endpos $1}
clock_expr0 :
| delim_clock_expr0 {$1}
| first=delim_clock_expr ; exprs=nonempty_list(preceded(AND, delim_clock_expr)) { CIntersection (first::exprs) }
| first=delim_clock_expr ; exprs=nonempty_list(preceded(OR, delim_clock_expr)) { CUnion (first::exprs) }
| first=delim_clock_expr ; exprs=nonempty_list(preceded(XOR, delim_clock_expr)) ; ratios=option(delimited(LBRACKET, var, RBRACKET)) { CDisjUnion {args=(first::exprs); ratios} }
| arg=delim_clock_expr ; DOLLAR ; delay=inline_relation(int_expr) ; on=option(ON ; e=delim_clock_expr {e}) { CTickDelay {arg;delay;on} }
| NEXT ; arg=delim_clock_expr {CNext arg}
| skip=option(skip) ; EVERY ; period=inline_relation(int_expr) ; OF ; base=delim_clock_expr { CPeriodic {skip;period;base}}
| SAMPLE ; arg=delim_clock_expr ; ON ; base=delim_clock_expr { CSample{arg;base} }
| base=delim_clock_expr ; EXCEPT ; subs=list(delim_clock_expr) { CMinus {base;subs}}
| FASTEST ; OF ; clocks=list(delim_clock_expr) { CFastest clocks }
| SLOWEST ; OF ; clocks=list(delim_clock_expr) { CSlowest clocks }
| PERIODIC ; period=duration ; WITH ; JITTER ; error=inline_relation(duration_expr) ; offset=option(offset) { CPeriodJitter {period;error;offset}}
| PERIODIC ; period=duration ; WITH ; DRIFT ; error=inline_relation(duration_expr) ; offset=option(offset) { CPeriodDrift {period;error;offset}}
| DELAY ; arg=delim_clock_expr ; BY ; delay=inline_relation(duration_expr) {CTimeDelay {arg;delay}}
| strict=option(STRICT) ; SPORADIC ; at_least=duration {CSporadic {at_least; strict=(Option.is_some strict)}} 


statement : statement0 {Loc.make $symbolstartpos $endpos $1}
statement0 : 
| VAR ; decls=separated_nonempty_list(COMMA, separated_pair(separated_nonempty_list(COMMA, id), COLON, var_type)) { VariableDeclaration decls }
| INTEGER ; COLON ; e=int_expr ; l=pair(num_rel,int_expr)+ {IntRelation (e,l)}
| DURATION ; COLON ; e=duration_expr ; l=pair(num_rel,duration_expr)+ {DurationRelation (e,l)}
| e1=clock_expr ; r=clock_rel ; e2=clock_expr {ClockRelation (e1,r,e2)}
| CONTINUOUS ; PROCESS ; var=var ; WITH ; dist=contdist {ContinuousProcess { var ; dist } }
| DISCRETE ; PROCESS ; var=var ; WITH ; values=located(list(INT)) ; SIM ; ratios=located(separated_list(COLON, INT)) { DiscreteProcess { var ; values ; ratios }}
| MUTEX ; pairs=delimited(LBRACE, dangling_list(COMMA, separated_pair(clock_expr, ARROWRIGHT, clock_expr)), RBRACE) { (Pool (1, pairs))}
| POOL ; n=INT; pairs=delimited(LBRACE, dangling_list(COMMA, separated_pair(clock_expr, ARROWRIGHT, clock_expr)), RBRACE) { (Pool (n, pairs))}
| name=id ; LBRACE ; statements=statements ; RBRACE { Block {name ; statements } }

statements :
| dangling_list(SEMICOLON, statement) { $1 }

%inline mod_block (NAME) : r=preceded(NAME, delimited(LBRACE, statements, RBRACE)) {r}

top_module : assumptions=list(mod_block(ASSUME)); structure=mod_block(STRUCTURE); assertions=list(mod_block(ASSERT)) ; EOF { {assumptions; structure; assertions} }
