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
%token INTEGER DURATION
%token ASSUME ASSERT STRUCTURE (*modules*)
%token AT QUESTION (* special syntax inside modules *)
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
%start top_module statements

%%

%inline addsub :
| PLUS {`Add}
| MINUS {`Sub}

%inline binop :
| PLUS {`Add}
| MINUS {`Sub}
| STAR {`Mul}
| SLASH {`Div}

%inline num_rel :
| LESS {`Less}
| LESSEQ {`LessEq}
| EQUAL {`Eq}
| MORE {`More}
| MOREEQ {`MoreEq}
| NOTEQUAL {`Neq}

count(X): {0} | X ; next=count(X) { next+1 }

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

%inline duration : value=DECIMAL ; scale=SECOND { Second { value ; scale=(Number.Rational.from_pair scale) } }

interval(X) :
| LBRACKET ; left=X ; right=X ; RBRACKET { Interval {left_strict=false; left; right; right_strict=false} }
| RBRACKET ; left=X ; right=X ; RBRACKET { Interval {left_strict=true; left; right; right_strict=false} }
| LBRACKET ; left=X ; right=X ; LBRACKET { Interval {left_strict=false; left; right; right_strict=true} }
| RBRACKET ; left=X ; right=X ; LBRACKET { Interval {left_strict=true; left; right; right_strict=true} }
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
| var { Loc.make $symbolstartpos $endpos @@ InlineVariable $1 }
| interval(X)  { Loc.make $symbolstartpos $endpos @@ InlineInterval $1 }

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
| skip=option(preceded(SKIP, inline_relation(int_expr))) ; EVERY ; period=inline_relation(int_expr) ; OF ; base=delim_clock_expr { CPeriodic {skip;period;base}}
| SAMPLE ; arg=delim_clock_expr ; ON ; base=delim_clock_expr { CSample{arg;base} }
| base=delim_clock_expr ; EXCEPT ; subs=list(delim_clock_expr) { CMinus {base;subs}}
| FASTEST ; OF ; clocks=list(delim_clock_expr) ; RPAREN { CFastest clocks }
| SLOWEST ; OF ; clocks=list(delim_clock_expr) ; RPAREN { CSlowest clocks }
| PERIODIC ; period=duration ; WITH ; JITTER ; error=inline_relation(duration_expr) ; offset=option(preceded(OFFSET, duration)) { CPeriodJitter {period;error;offset}}
| PERIODIC ; period=duration ; WITH ; DRIFT ; error=inline_relation(duration_expr) ; offset=option(preceded(OFFSET, duration)) { CPeriodDrift {period;error;offset}}
| DELAY ; arg=delim_clock_expr ; BY ; delay=inline_relation(duration_expr) {CTimeDelay {arg;delay}}
| strict=option(STRICT) ; SPORADIC ; at_least=duration {CSporadic {at_least; strict=(Option.is_some strict)}} 


statement : statement0 {Loc.make $symbolstartpos $endpos $1}
%inline statement0 : 
| INTEGER ; COLON ; e=int_expr ; l=pair(num_rel,int_expr)+ {IntRelation (e,l)}
| DURATION ; COLON ; e=duration_expr ; l=pair(num_rel,duration_expr)+ {DurationRelation (e,l)}
| e1=clock_expr ; r=clock_rel ; e2=clock_expr {ClockRelation (e1,r,e2)}
| CONTINUOUS ; PROCESS ; var=var ; WITH ; dist=contdist {ContinuousProcess { var ; dist } }
| DISCRETE ; PROCESS ; var=var ; WITH ; values=located(list(INT)) ; SIM ; ratios=located(separated_list(COLON, INT)) { DiscreteProcess { var ; values ; ratios }}
| MUTEX ; pairs=delimited(LBRACE, dangling_list(COMMA, separated_pair(clock_expr, ARROWRIGHT, clock_expr)), RBRACE) { (Pool (1, pairs))}
| POOL ; n=INT; pairs=delimited(LBRACE, dangling_list(COMMA, separated_pair(clock_expr, ARROWRIGHT, clock_expr)), RBRACE) { (Pool (n, pairs))}
| name=id ; LBRACE ; statements=statements ; RBRACE { Block {name ; statements } }

statements :
| separated_list(SEMICOLON+, statement) { $1 }

%inline mod_block (NAME) : r=preceded(NAME, delimited(LBRACE, statements, RBRACE)) {r}

top_module : assumptions=list(mod_block(ASSUME)); structure=mod_block(STRUCTURE); assertions=list(mod_block(ASSERT)) { {assumptions; structure; assertions} }
