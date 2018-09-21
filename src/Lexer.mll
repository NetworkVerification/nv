
{
  open Parser
  open Printf
  open Span
  exception Eof

  let position lexbuf =
    {start=Lexing.lexeme_start lexbuf; finish=Lexing.lexeme_end lexbuf}

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <-
      { pos with Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
                 Lexing.pos_bol = pos.Lexing.pos_cnum; } ;;

}

let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*
let symbol = ['~' '`' '!' '@' '#' '$' '%' '^' '&' '|' ':' '?' '>' '<' '[' ']' '=' '-' '.']+
let num = ['0'-'9']+
let width = "u"num
let tid = ['\'']['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule token = parse
  | "(*"              { comments 0 lexbuf }
  | "false"           { FALSE (position lexbuf) }
  | "true"            { TRUE (position lexbuf) }
  | "let"             { LET (position lexbuf) }
  | "in"              { IN (position lexbuf) }
  | "if"              { IF (position lexbuf) }
  | "then"            { THEN (position lexbuf) }
  | "else"            { ELSE (position lexbuf) }
  | "fun"             { FUN (position lexbuf) }
  | "symbolic"        { SYMBOLIC (position lexbuf) }
  | "None"            { NONE (position lexbuf) }
  | "Some"            { SOME (position lexbuf) }
  | "edges"           { EDGES (position lexbuf) }
  | "nodes"           { NODES (position lexbuf) }
  | "match"           { MATCH (position lexbuf) }
  | "with"            { WITH (position lexbuf) }
  | "require"         { REQUIRE (position lexbuf) }
  | "createDict"      { CREATEMAP (position lexbuf) }
  | "map"             { MAP (position lexbuf) }
  | "mapIf"           { MAPIF (position lexbuf) }
  | "combine"         { COMBINE (position lexbuf) }
  | "union"           { UNION (position lexbuf) }
  | "inter"           { INTER (position lexbuf) }
  | "filter"          { FILTER (position lexbuf) }
  | "minus"           { MINUS (position lexbuf) }
  | "set"             { TSET (position lexbuf) }
  | "dict"            { TDICT (position lexbuf) }
  | "option"          { TOPTION (position lexbuf) }
  | "int" width as s  { TINT (position lexbuf, Z.of_string @@ Str.lchop ~n:4 s) }
  | "int"             { TINT (position lexbuf, Z.of_int 32) }
  | "bool"            { TBOOL (position lexbuf) }
  | "type"            { TYPE (position lexbuf) }
  | "attribute"       { ATTRIBUTE (position lexbuf) }
  | id as s           { ID (position lexbuf, Var.create s) }
  | num width as n    { NUM (position lexbuf, Integer.of_string n) }
  | num as n          { NUM (position lexbuf, Integer.of_string n) }
  | "&&"              { AND (position lexbuf) }
  | "||"              { OR (position lexbuf) }
  | "|"               { BAR (position lexbuf) }
  | "->"              { ARROW (position lexbuf) }
  | "!"               { NOT (position lexbuf) }
  | ","               { COMMA (position lexbuf) }
  | "+" width as s    { PLUS (position lexbuf, Z.of_string @@ Str.lchop ~n:2 s) }
  | "+"               { PLUS (position lexbuf, Z.of_int 32) }
  | "-" width as s    { SUB (position lexbuf, Z.of_string @@ Str.lchop ~n:2 s) }
  | "-"               { SUB (position lexbuf, Z.of_int 32) }
  | "<="              { LEQ (position lexbuf) }
  | ">="              { GEQ (position lexbuf) }
  | "="               { EQ (position lexbuf) }
  | "<"               { LESS (position lexbuf) }
  | ">"               { GREATER (position lexbuf) }
  | ";"               { SEMI (position lexbuf) }
  | ":"               { COLON (position lexbuf) }
  | "("               { LPAREN (position lexbuf) }
  | ")"               { RPAREN (position lexbuf) }
  | "["               { LBRACKET (position lexbuf) }
  | "]"               { RBRACKET (position lexbuf) }
  | "{"               { LBRACE (position lexbuf) }
  | "}"               { RBRACE (position lexbuf) }
  | "_"               { UNDERSCORE (position lexbuf) }
  | [' ' '\t']        { token lexbuf }
  | '\n'              { incr_linenum lexbuf; token lexbuf}
  | _ as c            { printf "[Parse Error] Unrecognized character: %c\n" c; token lexbuf }
  | eof		            { EOF }

and comments level = parse
  | "*)"  { if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "(*"  { comments (level+1) lexbuf }
  | '\n'  { incr_linenum lexbuf; comments level lexbuf}
  | _     { comments level lexbuf }
  | eof   { raise End_of_file }
