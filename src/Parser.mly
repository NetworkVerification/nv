%{
  open Syntax

  let exp e span : exp = aexp (e, None, span)

  let value v span : value = avalue (v, None, span)

  let to_value v span : exp = exp (e_val (value v span)) span

  let tuple_it es (span : Span.t) : exp =
    match es with
    | [e] -> exp e span
    | es -> exp (etuple es) span

  let tuple_pattern ps =
    match ps with
    | [p] -> p
    | ps -> PTuple ps

  (* TODO: span not calculated correctly here? *)
  let rec make_fun params (body : exp) (body_span: Span.t) (span : Span.t) : exp =
    match params with
	| [] -> body
	| (x,tyopt)::rest ->
        let e = efun {arg=x; argty=tyopt; resty=None; body=make_fun rest body body_span body_span} in
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
    let tru = exp (e_val (value (vbool true) span)) span in
    let rec updates e exprs =
        match exprs with
        | [] -> e
        | expr :: tl ->
            let e = exp (eop MSet [e; expr; tru]) span in
            updates e tl
    in
    let e = exp (e_val (value (vbool false) span)) span in
    let e = exp (eop MCreate [e]) span in
    updates e exprs

%}

%token <Span.t * Var.t> ID
%token <Span.t * Integer.t> NUM
%token <Span.t> AND
%token <Span.t> OR
%token <Span.t> NOT
%token <Span.t> TRUE
%token <Span.t> FALSE
%token <Span.t * int> PLUS
%token <Span.t * int> SUB
%token <Span.t> EQ
%token <Span.t * int> LESS
%token <Span.t * int> GREATER
%token <Span.t * int> LEQ
%token <Span.t * int> GEQ
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
%token <Span.t * int> TINT
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
   | TINT                               { Syntax.TInt (snd $1) }
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
    | SYMBOLIC ID COLON ty EQ expr      { let ety = exp (ety $6 $4) $6.espan in
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
                                          exp (elet id e $6) span }
    | LET LPAREN patterns RPAREN EQ expr IN expr
                                        { let p = tuple_pattern $3 in
                                          let e = ematch $6 [(p,$8)] in
                                          let span = Span.extend $1 $8.espan in
                                          exp e span }
    | IF expr THEN expr ELSE expr       { exp (eif $2 $4 $6) (Span.extend $1 $6.espan) }
    (* TODO: span does not include the branches here *)
    | MATCH expr WITH branches          { exp (ematch $2 $4) (Span.extend $1 $3) }
    | FUN params ARROW expr             { make_fun $2 $4 $4.espan (Span.extend $1 $4.espan) }
    | MAP exprsspace                    { exp (eop MMap $2) $1 }
    | MAPIF exprsspace                  { exp (eop MMapFilter $2) $1 }
    | COMBINE exprsspace                { exp (eop MMerge $2) $1 }
    | CREATEMAP exprsspace              { exp (eop MCreate $2) $1 }
    | SOME expr                         { exp (esome $2) (Span.extend $1 $2.espan) }
    | NOT expr                          { exp (eop Not [$2]) (Span.extend $1 $2.espan) }
    | expr AND expr                     { exp (eop And [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr OR expr                      { exp (eop Or [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr PLUS expr                    { exp (eop (UAdd (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr SUB expr                     { exp (eop (USub (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr EQ expr                      { exp (eop UEq [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr LESS expr                    { exp (eop (ULess (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GREATER expr                 { exp (eop (ULess (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | expr LEQ expr                     { exp (eop (ULeq (snd $2)) [$1;$3]) (Span.extend $1.espan $3.espan) }
    | expr GEQ expr                     { exp (eop (ULeq (snd $2)) [$3;$1]) (Span.extend $1.espan $3.espan) }
    | LPAREN expr COLON ty RPAREN       { exp (ety $2 $4) (Span.extend $1 $5) }
    | expr LBRACKET expr RBRACKET               { exp (eop MGet [$1;$3]) (Span.extend $1.espan $4) }
    | expr LBRACKET expr COLON EQ expr RBRACKET { exp (eop MSet [$1;$3;$6]) (Span.extend $1.espan $7) }
    | expr UNION expr                   { let el0 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let el1 = exp (e_val (voption (Some (vbool true)))) $2 in
                                          let er0 = el0 in
                                          let er1 = el1 in
                                          let varx = Var.fresh "x" in
                                          let vary = Var.fresh "y" in
                                          let x = exp (evar varx) $2 in
                                          let y = exp (evar vary) $2 in
                                          let e = exp (eop Or [x;y]) $2 in
                                          let e = exp (efun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (efun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (eop MMerge [e;$1;$3;el0;el1;er0;er1]) (Span.extend $1.espan $3.espan) }
    | expr INTER expr                   { let el0 = exp (e_val (voption (Some (vbool true)))) $2 in
                                          let el1 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let er0 = el0 in
                                          let er1 = el1 in
                                          let varx = Var.create "x" in
                                          let vary = Var.create "y" in
                                          let x = exp (evar varx) $2 in
                                          let y = exp (evar vary) $2 in
                                          let e = exp (eop And [x;y]) $2 in
                                          let e = exp (efun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (efun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (eop MMerge [e;$1;$3;el0;el1;er0;er1]) (Span.extend $1.espan $3.espan) }
    | expr MINUS expr                   { let el0 = exp (e_val (voption None)) $2 in
                                          let el1 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let er0 = exp (e_val (voption (Some (vbool false)))) $2 in
                                          let er1 = el0 in
                                          let varx = Var.create "x" in
                                          let vary = Var.create "y" in
                                          let x = exp (evar varx) $2 in
                                          let y = exp (evar vary) $2 in
                                          let e = exp (eop Not [y]) $2 in
                                          let e = exp (eop And [x;e]) $2 in
                                          let e = exp (efun {arg=vary;argty=None;resty=None;body=e}) $2 in
                                          let e = exp (efun {arg=varx;argty=None;resty=None;body=e}) $2 in
                                          exp (eop MMerge [e;$1;$3;el0;el1;er0;er1]) (Span.extend $1.espan $3.espan) }
    | FILTER exprsspace                 { let span = $1 in
                                          let vark = Var.create "k" in
                                          let e = exp (e_val (value (vbool false) span)) span in
                                          let e = exp (efun {arg=vark;argty=None;resty=None;body=e}) span in
                                          let args = match $2 with hd :: tl -> hd::e::tl | _ -> [e] in
                                          exp (eop MMapFilter args) $1 }
    | LBRACE exprs RBRACE               { make_set $2 (Span.extend $1 $3) }
    | LBRACE RBRACE                     { make_set [] (Span.extend $1 $2) }
    | expr2                             { $1 }
;

expr2:
    | expr2 expr3                       { exp (eapp $1 $2) (Span.extend $1.espan $2.espan) }
    | expr3                             { $1 }
;

expr3:
    | ID                                { exp (evar (snd $1)) (fst $1) }
    | NUM                               { to_value (vint (snd $1)) (fst $1) }
    | TRUE                              { to_value (vbool true) $1 }
    | FALSE                             { to_value (vbool false) $1 }
    | NONE                              { to_value (voption None) $1 }
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
    | NUM                               { PInt (snd $1) }
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
