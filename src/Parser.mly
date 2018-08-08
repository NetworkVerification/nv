%{
  open Syntax
  open Unsigned

  let exp e span : exp = {e=e; ety=None; espan=span}

  let value v span : value = {v=v; vty=None; vspan=span}

  let e_val v span : exp = exp (EVal (value v span)) span

  let tuple_it es (span : Span.t) : exp =
    match es with
    | [e] -> exp e.e span
    | es -> exp (ETuple es) span

  let tuple_pattern ps =
    match ps with
    | [p] -> p
    | ps -> PTuple ps

  (* TODO: span not calculated correctly here? *)
  let rec make_fun params (body : exp) (body_span: Span.t) (span : Span.t) : exp =
    match params with
	| [] -> body
	| (x,tyopt)::rest -> 
        let e = EFun {arg=x; argty=tyopt; resty=None; body=make_fun rest body body_span body_span} in
        exp e span
    
  let local_let (id,params) body body_span span =
    (id, make_fun params body body_span span)

  let merge_identifier = "merge"
  let trans_identifier = "trans"
  let init_identifier = "init"
  let assert_identifier = "assert"
    
  let global_let (id,params) body body_span span =
    let e = make_fun params body body_span span in
    if Var.name id = merge_identifier then
      DMerge e
    else if Var.name id = trans_identifier then
      DTrans e
    else if Var.name id = init_identifier then
      DInit e
    else if Var.name id = assert_identifier then 
      DAssert e
    else
      DLet (id, None, e)
  
%}

%token <Span.t * Var.t> ID
%token <Span.t * Unsigned.UInt32.t> NUM
%token <Span.t> AND 
%token <Span.t> OR 
%token <Span.t> NOT 
%token <Span.t> TRUE 
%token <Span.t> FALSE
%token <Span.t> PLUS
%token <Span.t> SUB
%token <Span.t> EQ
%token <Span.t> LESS
%token <Span.t> GREATER
%token <Span.t> LEQ
%token <Span.t> GEQ 
%token <Span.t> LET 
%token <Span.t> IN 
%token <Span.t> IF 
%token <Span.t> THEN 
%token <Span.t> ELSE 
%token <Span.t> FUN
%token <Span.t> SOME 
%token <Span.t> NONE 
%token <Span.t> MATCH 
%token <Span.t> WITH
%token <Span.t> BAR 
%token <Span.t> ARROW 
%token <Span.t> DOTDOT
%token <Span.t> SEMI 
%token <Span.t> LPAREN 
%token <Span.t> RPAREN 
%token <Span.t> LBRACKET 
%token <Span.t> RBRACKET 
%token <Span.t> LBRACE 
%token <Span.t> RBRACE 
%token <Span.t> COMMA 
%token <Span.t> UNDERSCORE 
%token <Span.t> CREATEMAP
%token <Span.t> MAP
%token <Span.t> FILTER
%token <Span.t> COMBINE
%token <Span.t> TOPTION 
%token <Span.t> TDICT
%token <Span.t> ATTRIBUTE 
%token <Span.t> TYPE 
%token <Span.t> COLON 
%token <Span.t> TBOOL 
%token <Span.t> TINT
%token <Span.t> EDGES 
%token <Span.t> NODES
%token <Span.t> SYMBOLIC
%token EOF

%start prog
%type  <Syntax.declarations> prog

%start expreof
%type <Syntax.exp> expreof

%right ELSE IN     /* lowest precedence */
%right ARROW 
%nonassoc GEQ GREATER LEQ LESS EQ
%left PLUS SUB      
%left AND OR 
%right NOT
%right SOME
%left LBRACKET      /* highest precedence */

%%

ty: 
   | ty ARROW ty                        { TArrow ($1,$3) }
   | TBOOL                              { TBool }
   | TINT                               { Syntax.tint }
   | LPAREN tys RPAREN                  { if List.length $2 = 1 then List.hd $2 else TTuple $2 }
   | TOPTION LBRACKET ty RBRACKET       { TOption $3 }
   | TDICT LBRACKET ty COMMA ty RBRACKET{ TMap ($3,$5) }
;

tys: 
  | ty                                  { [$1] }
  | ty COMMA tys                        { $1::$3 }
;
(* 
ty:
   | ty1                                { $1 }
;

ty1:
   | ty2                                { $1 }
   | ty2 ARROW ty1                      { TArrow ($1, $3) }
;

ty2:
   | ty3                                { $1 }
   | tuple                              { TTuple $1 }
;

tuple:
   | ty3 STAR ty3                       { [$1;$3] }
   | ty3 STAR tuple                     { $1::$3 }
;

ty3:
   | ty4                                { $1 }
   | TOPTION LBRACKET ty3 RBRACKET      { TOption $3 }
   | TDICT LBRACKET ty3 RBRACKET        {TMap $3}
;

ty4:
   | TBOOL                              { TBool }
   | TINT                               { Syntax.tint }
   | LPAREN ty RPAREN                   { $2 }
;
*)

param:
   | ID                                 { (snd $1, None) }
   | LPAREN ID COLON ty RPAREN          { (snd $2, Some $4) }
;

params:
    | param                             { [$1] }
    | param params                      { $1::$2 }
;
  
letvars:
    | ID                                { (snd $1,[]) }
    | ID params                         { (snd $1, $2) }
;

component:
    | LET letvars EQ expr               { global_let $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | SYMBOLIC ID EQ expr               { DSymbolic (snd $2, $4) }
    | LET EDGES EQ LBRACE RBRACE        { DEdges [] }
    | LET EDGES EQ LBRACE edges RBRACE  { DEdges $5 }
    | LET NODES EQ NUM                  { DNodes (snd $4) }
    | TYPE ATTRIBUTE EQ ty              { DATy $4 }
;
  
components:
    | component                         { [$1] }
    | component components              { $1 :: $2 }
;

expreof:
    expr EOF    { $1 }        
;

expr:
    | LET letvars EQ expr IN expr       { let span = (Span.extend $1 $6.espan) in
                                          let (id, e) = local_let $2 $4 $4.espan span in 
                                          exp (ELet (id, e, $6)) span }
    | IF expr THEN expr ELSE expr       { exp (EIf ($2, $4, $6)) (Span.extend $1 $6.espan) }
    (* TODO: span does not include the branches here *)
    | MATCH expr WITH branches          { exp (EMatch ($2, $4)) (Span.extend $1 $3) }
    | FUN params ARROW expr             { make_fun $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | MAP exprsspace                    { exp (EOp (MMap, $2)) $1 }
    | FILTER exprsspace                 { exp (EOp (MFilter, $2)) $1 }
    | COMBINE exprsspace                { exp (EOp (MMerge, $2)) $1 }
    | CREATEMAP exprsspace              { exp (EOp (MCreate, $2)) $1 }
    | SOME expr                         { exp (ESome $2) (Span.extend $1 $2.espan) }
    | NOT expr                          { exp (EOp (Not,[$2])) (Span.extend $1 $2.espan) }
    | expr AND expr                     { exp (EOp (And, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr OR expr                      { exp (EOp (Or, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr PLUS expr                    { exp (EOp (UAdd, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr SUB expr                     { exp (EOp (USub, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr EQ expr                      { exp (EOp (UEq, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr LESS expr                    { exp (EOp (ULess, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr GREATER expr                 { exp (EOp (ULess, [$3;$1])) (Span.extend $1.espan $3.espan) }
    | expr LEQ expr                     { exp (EOp (ULeq, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr GEQ expr                     { exp (EOp (ULeq, [$3;$1])) (Span.extend $1.espan $3.espan) }
    | LPAREN expr COLON ty RPAREN       { exp (ETy ($2, $4)) (Span.extend $1 $5) }
    | expr LBRACKET expr RBRACKET               { exp (EOp (MGet, [$1;$3])) (Span.extend $1.espan $4) }
    | expr LBRACKET expr COLON EQ expr RBRACKET { exp (EOp (MSet, [$1;$3;$6])) (Span.extend $1.espan $7) }
    | expr LBRACKET expr DOTDOT expr RBRACKET   
                                        { let var = Var.create "k" in
                                          let evar = exp (EVar var) (Span.extend $2 $6) in
                                          let span = (Span.extend $1.espan $3.espan) in 
                                          let lower = exp (EOp (ULeq, [$3; evar;])) span in
                                          let upper = exp (EOp (ULeq, [evar; $5])) span in
                                          let range = exp (EOp (And, [lower; upper])) span in
                                          let span = (Span.extend $1.espan $6) in
                                          let e = exp (EFun {arg=var; argty=None; resty=None; body=range}) span in
                                          exp (EOp (MFilter, [e])) span }
    | expr2                             { $1 }
;

expr2:
    | expr2 expr3                       { exp (EApp ($1, $2)) (Span.extend $1.espan $2.espan) }
    | expr3                             { $1 }
;

expr3:
    | ID                                { exp (EVar (snd $1)) (fst $1) }
    | NUM                               { e_val (VUInt32 (snd $1)) (fst $1) }
    | TRUE                              { e_val (VBool true) $1 }
    | FALSE                             { e_val (VBool false) $1 }
    | NONE                              { e_val (VOption None) $1 }
    | LPAREN exprs RPAREN               { tuple_it $2 (Span.extend $1 $3) }
;
	
exprs:
    | expr                              { [$1] }
    | expr COMMA exprs                  { $1 :: $3 }
;

exprsspace:
    | expr3                             { [$1] }
    | expr3 exprsspace                  { $1 :: $2 }
;

edge:
    | NUM SUB NUM SEMI                  { [(snd $1, snd $3)] }
    | NUM EQ NUM SEMI                   { [(snd $1, snd $3); (snd $3, snd $1)] }
;

edges:
    | edge                              { $1 }
    | edge edges                        { $1 @ $2 }
;

pattern:
    | UNDERSCORE                        { PWild }
    | ID                                { PVar (snd $1) }
    | TRUE                              { PBool true }
    | FALSE                             { PBool false }
    | NUM                               { PUInt32 (snd $1) }
    | LPAREN patterns RPAREN            { tuple_pattern $2 }
    | NONE                              { POption None }
    | SOME pattern                      { POption (Some $2) }
;

patterns:
    | pattern                           { [$1] }
    | pattern COMMA patterns            { $1::$3 }
;

branch:
    | BAR pattern ARROW expr            { ($2, $4) }
;

branches:
    | branch                            { [$1] }
    | branch branches                   { $1::$2 }
;

prog:
    | components EOF                    { $1 }
;