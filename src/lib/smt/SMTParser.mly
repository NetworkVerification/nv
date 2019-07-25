%{
  open Nv_core.Syntax

%}

%token <Nv_datatypes.Integer.t> NUM
%token <string> ID
%token TRUE
%token FALSE
%token UNIT
%token SOME
%token NONE
%token AS
%token PAIR
%token LPAREN
%token RPAREN
%token NEG

%token EOF

%start smtlib
%type <Nv_core.Syntax.value> smtlib


%%
junk:
| ID					{ }
| LPAREN junk*	RPAREN			{ }
;

value:
    | NUM                               { vint $1 }
    | LPAREN NEG NUM RPAREN             { vint $3 }
    | TRUE				{ vbool true }
    | FALSE				{ vbool false }
    | NONE				{ voption None }
    | UNIT        { vunit () }
;

values:
    | value				{ $1 }
    | LPAREN SOME values RPAREN		{ voption (Some $3) }
    | LPAREN AS NONE junk* RPAREN	{ voption None }
    | LPAREN PAIR valuesList RPAREN     { vtuple $3 }
;

valuesList:
    | values				{ [$1] }
    | values valuesList			{ $1 :: $2 }
;

smtlib:
    | values EOF			{ $1 }
