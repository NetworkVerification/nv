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

  let make_set exprs span = 
    let tru = exp (EVal (value (VBool true) span)) span in
    let rec updates e exprs = 
        match exprs with 
        | [] -> e
        | expr :: tl -> 
            let e = exp (EOp (MSet, [e; expr; tru])) span in 
            updates e tl
    in
    let e = exp (EVal (value (VBool false) span)) span in
    let e = exp (EOp (MCreate, [e])) span in
    updates e exprs
  
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
%token <Span.t> MAPIF
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
%token <Span.t> REQUIRE
%token <Span.t> UNION
%token <Span.t> INTER
%token <Span.t> MINUS
%token <Span.t> FILTER
%token <Span.t> TSET

%token EOF

%start prog
%type  <Syntax.declarations> prog

%start expreof
%type <Syntax.exp> expreof

%right ELSE IN     /* lowest precedence */
%right ARROW 
%left AND OR 
%nonassoc GEQ GREATER LEQ LESS EQ
%left PLUS SUB UNION INTER MINUS  
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
   | TSET LBRACKET ty RBRACKET          { TMap ($3,TBool) }
;

tys: 
  | ty                                  { [$1] }
  | ty COMMA tys                        { $1::$3 }
;

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
    | SYMBOLIC ID EQ expr               { DSymbolic (snd $2, Exp $4) }
    | SYMBOLIC ID COLON ty              { DSymbolic (snd $2, Ty $4) }
    | SYMBOLIC ID COLON ty EQ expr      { let ety = exp (ETy ($6, $4)) $6.espan in
                                          DSymbolic (snd $2, Exp ety) }
    | REQUIRE expr                      { DRequire $2 }
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
    | LET LPAREN patterns RPAREN EQ expr IN expr
                                        { let p = tuple_pattern $3 in 
                                          let e = EMatch ($6, [(p,$8)]) in 
                                          let span = Span.extend $1 $8.espan in 
                                          exp e span }
    | IF expr THEN expr ELSE expr       { exp (EIf ($2, $4, $6)) (Span.extend $1 $6.espan) }
    (* TODO: span does not include the branches here *)
    | MATCH expr WITH branches          { exp (EMatch ($2, $4)) (Span.extend $1 $3) }
    | FUN params ARROW expr             { make_fun $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | MAP exprsspace                    { exp (EOp (MMap, $2)) $1 }
    | MAPIF exprsspace                  { exp (EOp (MMapFilter, $2)) $1 }
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
    | expr UNION expr                   { let varx = Var.fresh "x" in 
                                          let vary = Var.fresh "y" in
                                          let x = exp (EVar varx) $2 in 
                                          let y = exp (EVar vary) $2 in
                                          let e = exp (EOp (Or, [x;y])) $2 in
                                          let e = exp (EFun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (EFun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (EOp (MMerge, [e;$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr INTER expr                   { let varx = Var.create "x" in 
                                          let vary = Var.create "y" in
                                          let x = exp (EVar varx) $2 in 
                                          let y = exp (EVar vary) $2 in
                                          let e = exp (EOp (And, [x;y])) $2 in
                                          let e = exp (EFun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (EFun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (EOp (MMerge, [e;$1;$3])) (Span.extend $1.espan $3.espan) }
    | expr MINUS expr                   { let varx = Var.create "x" in 
                                          let vary = Var.create "y" in
                                          let x = exp (EVar varx) $2 in 
                                          let y = exp (EVar vary) $2 in
                                          let e = exp (EOp (Not, [y])) $2 in
                                          let e = exp (EOp (And, [x;e])) $2 in
                                          let e = exp (EFun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (EFun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (EOp (MMerge, [e;$1;$3])) (Span.extend $1.espan $3.espan) }
    | FILTER exprsspace                 { let span = $1 in
                                          let vark = Var.create "k" in 
                                          let e = exp (EVal (value (VBool false) span)) span in
                                          let e = exp (EFun {arg=vark;argty=None;resty=None;body=e}) span in
                                          let args = match $2 with hd :: tl -> hd::e::tl | _ -> [e] in
                                          exp (EOp (MMapFilter, args)) $1 }
    | LBRACE exprs RBRACE               { make_set $2 (Span.extend $1 $3) }
    | LBRACE RBRACE                     { make_set [] (Span.extend $1 $2) }
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