%{
  open Syntax
  open Unsigned
        
%}

%token <Unsigned.UInt32.t> NUM
%token <string> ID
%token TRUE 
%token FALSE
%token SOME 
%token NONE
%token AS
%token PAIR 
%token LPAREN 
%token RPAREN 

%token EOF

%start smtlib
%type <Syntax.value> smtlib


%%
junk:
| ID					{ }
| LPAREN junk*	RPAREN			{ }
;

value:
    | NUM                               { vint $1 }
    | TRUE				{ vbool true }
    | FALSE				{ vbool false }
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