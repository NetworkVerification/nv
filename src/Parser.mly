%{
  open Syntax
  open Unsigned

  let exp e span : exp = {e=e; ety=None; espan=span}

  let value v span : value = {v=v; vty=None; vspan=span}

  let e_val v span : exp = exp (EVal (value v span)) span

  let tuple_it es (span : Span.t) : exp =
    match es with
    | [e] -> e
    | es -> exp (ETuple es) span

  let tuple_pattern ps =
    match ps with
    | [p] -> p
    | ps -> PTuple ps

  (* TODO: span not calculated correctly here? *)
  let rec make_fun params (body : exp) (span : Span.t) : exp =
    match params with
	| [] -> body
	| (x,tyopt)::rest -> 
        let e = EFun {arg=x;argty=tyopt;resty=None;body=make_fun rest body span} in
        exp e span
    
  let local_let (id,params) body span =
    (id, make_fun params body span)

  let merge_identifier = "merge"
  let trans_identifier = "trans"
  let init_identifier = "init"
    
  let global_let (id,params) body span =
    let e = make_fun params body span in
    if Var.name id = merge_identifier then
      DMerge e
    else if Var.name id = trans_identifier then
      DTrans e
    else if Var.name id = init_identifier then
      DInit e
    else
      DLet (id, make_fun params body span)
  
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
%token <Span.t> DOT 
%token <Span.t> BAR 
%token <Span.t> ARROW 
%token <Span.t> SEMI 
%token <Span.t> LPAREN 
%token <Span.t> RPAREN 
%token <Span.t> LBRACKET 
%token <Span.t> RBRACKET 
%token <Span.t> LBRACE 
%token <Span.t> RBRACE 
%token <Span.t> COMMA 
%token <Span.t> UNDERSCORE 
%token <Span.t> STAR 
%token <Span.t> TOPTION 
%token <Span.t> TVECTOR 
%token <Span.t> ATTRIBUTE 
%token <Span.t> TYPE 
%token <Span.t> COLON 
%token <Span.t> TBOOL 
%token <Span.t> TINT
%token <Span.t> EDGES 
%token <Span.t> NODES
%token EOF

%start prog
%type  <Syntax.declarations> prog

%start expr
%type <Syntax.exp> expr

%left PLUS SUB      /* lowest precedence */
%left AND OR
%right NOT
%left DOT
%left LBRACKET      /* highest precedence */

%%
ty:
   | ty1 { $1 }
;

ty1:
   | ty2 { $1 }
   | ty2 ARROW ty1 { TArrow ($1, $3) }
;

ty2:
   | ty3 { $1 }
   | tuple { TTuple $1 }
;

tuple:
   | ty3 STAR ty3   { [$1;$3] }
   | ty3 STAR tuple { $1::$3 }
;

ty3:
   | ty4             { $1 }
   | ty3 TOPTION     { TOption $1 }
   | ty3 TVECTOR LBRACKET NUM RBRACKET {TMap (snd $4, $1)}
;

ty4:
   | TBOOL          { TBool }
   | TINT           { Syntax.tint }
   | LPAREN ty RPAREN { $2 }
;

param:
   | ID                         { (snd $1, None) }
   | LPAREN ID COLON ty RPAREN  { (snd $2, Some $4) }
;

params:
    | param            { [$1] }
    | param params     { $1::$2 }
;
  
letvars:
    | ID        { (snd $1,[]) }
    | ID params { (snd $1, $2) }
;

component:
    | LET letvars EQ expr               { global_let $2 $4 (Span.extend $1 $4.espan) }
    | LET EDGES EQ LBRACE edges RBRACE  { DEdges $5 }
    | LET NODES EQ NUM                  { DNodes (snd $4) }
    | TYPE ATTRIBUTE EQ ty              { DATy $4 }
;
  
components:
    | component                           { [$1] }
    | component components                { $1 :: $2 }
;

expr:
    | expr1                               { $1 }
;

expr1:
    | expr2                               { $1 }
    | LET letvars EQ expr IN expr1        { let span = (Span.extend $1 $6.espan) in
                                            let (id, e) = local_let $2 $4 span in 
                                            exp (ELet (id, e, $6)) span }
    | IF expr1 THEN expr ELSE expr1       { exp (EIf ($2, $4, $6)) (Span.extend $1 $6.espan) }
    (* TODO: span not quite right here *)
    | MATCH expr WITH branches            { exp (EMatch ($2, $4)) (Span.extend $1 $3) }
    | FUN params ARROW expr1              { make_fun $2 $4 (Span.extend $1 $4.espan) }
;

expr2:
    | expr3                      { $1 }
    | expr2 expr3                { exp (EApp ($1, $2)) (Span.extend $1.espan $2.espan) }
    | SOME expr3                 { exp (ESome $2) (Span.extend $1 $2.espan) }
;

expr3:
    | expr4                                     { $1 }
    | NOT expr3                                 { exp (EOp (Not,[$2])) (Span.extend $1 $2.espan) }
    | expr3 AND expr4                           { exp (EOp (And, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr3 OR expr4                            { exp (EOp (Or, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr3 PLUS expr4                          { exp (EOp (UAdd, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr3 SUB expr4                           { exp (EOp (USub, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr4 EQ expr4                            { exp (EOp (UEq, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr4 LESS expr4                          { exp (EOp (ULess, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr4 GREATER expr4                       { exp (EOp (ULess, [$3;$1])) (Span.extend $1.espan $3.espan) }
    | expr4 LEQ expr4                           { exp (EOp (ULeq, [$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr4 GEQ expr4                           { exp (EOp (ULeq, [$3;$1])) (Span.extend $1.espan $3.espan) }
    | expr3 LBRACKET expr RBRACKET              { exp (EOp (MGet, [$1;$3])) (Span.extend $1.espan $4) }
    | expr3 LBRACKET expr EQ expr RBRACKET      { exp (EOp (MSet, [$1;$3;$5])) (Span.extend $1.espan $6) }
    | expr3 DOT NUM                             { exp (EProj (UInt32.to_int (snd $3), $1)) (Span.extend $1.espan (fst $3)) }
;

expr4:
    | ID                       { exp (EVar (snd $1)) (fst $1) }
    | NUM                      { e_val (VUInt32 (snd $1)) (fst $1) }
    | TRUE                     { e_val (VBool true) $1 }
    | FALSE                    { e_val (VBool false) $1 }
    | NONE                     { e_val (VOption (None,None)) $1 }
    | LPAREN exprs RPAREN      { tuple_it $2 (Span.extend $1 $3) }
    | LPAREN expr COLON ty RPAREN { exp (ETy ($2, $4)) (Span.extend $1 $5) }
;
	
exprs:
    | expr                     { [$1] }
    | expr COMMA exprs         { $1 :: $3 }
;

edge:
    | NUM SUB NUM SEMI         { [(snd $1, snd $3)] }
    | NUM EQ NUM SEMI          { [(snd $1, snd $3); (snd $3, snd $1)] }
;

edges:
    | edge                     { $1 }
    | edge edges               { $1 @ $2 }
;

pattern:
    | UNDERSCORE               { PWild }
    | ID                       { PVar (snd $1) }
    | TRUE                     { PBool true }
    | FALSE                    { PBool false }
    | NUM                      { PUInt32 (snd $1) }
    | LPAREN patterns RPAREN   { tuple_pattern $2 }
    | NONE                     { POption None }
    | SOME pattern             { POption (Some $2) }
;

patterns:
    | pattern                  { [$1] }
    | pattern COMMA patterns   { $1::$3 }
;

branch:
    | BAR pattern ARROW expr   { ($2, $4) }
;

branches:
    | branch                   { [$1] }
    | branch branches          { $1::$2 }
;

prog:
    | components EOF           { $1 }
;