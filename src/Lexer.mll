
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
let tid = ['\'']['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*
  
rule token = parse
  | "(*"         { comments 0 lexbuf }
  | "false"      { FALSE (position lexbuf) }
  | "true"       { TRUE (position lexbuf) }
  | "let"        { LET (position lexbuf) } 
  | "in"         { IN (position lexbuf) }
  | "if"         { IF (position lexbuf) }
  | "then"       { THEN (position lexbuf) }
  | "else"       { ELSE (position lexbuf) }
  | "fun"        { FUN (position lexbuf) }
  | "symbolic"   { SYMBOLIC (position lexbuf) }
  | "None"       { NONE (position lexbuf) }
  | "Some"       { SOME (position lexbuf) }
  | "edges"      { EDGES (position lexbuf) }
  | "nodes"      { NODES (position lexbuf) }
  | "match"      { MATCH (position lexbuf) }
  | "with"       { WITH (position lexbuf) }
  | "createMap"  { CREATEMAP (position lexbuf) }
  | "map"        { MAP (position lexbuf) }
  | "filter"     { FILTER (position lexbuf) }
  | "combine"    { COMBINE (position lexbuf) }
  | "dict"       { TDICT (position lexbuf) }
  | "option"     { TOPTION (position lexbuf) }
  | "int"        { TINT (position lexbuf) }
  | "bool"       { TBOOL (position lexbuf) }
  | "type"       { TYPE (position lexbuf) }
  | "attribute"  { ATTRIBUTE (position lexbuf) }
  | id as s      { ID (position lexbuf, Var.create s) }
  | num as n     { NUM (position lexbuf, Unsigned.UInt32.of_string n) }
  | "&&"         { AND (position lexbuf) }
  | "||"         { OR (position lexbuf) }
  | "|"          { BAR (position lexbuf) }
  | "->"         { ARROW (position lexbuf) }
  | ".."         { DOTDOT (position lexbuf) }
  | "!"          { NOT (position lexbuf) }
  | ","          { COMMA (position lexbuf) }
  | "+"          { PLUS (position lexbuf) }
  | "-"          { SUB (position lexbuf) }
  | "="          { EQ (position lexbuf) }
  | "<"          { LESS (position lexbuf) }
  | ">"          { GREATER (position lexbuf) }
  | ";"          { SEMI (position lexbuf) }
  | ":"          { COLON (position lexbuf) }
  | "("          { LPAREN (position lexbuf) }
  | ")"          { RPAREN (position lexbuf) }
  | "["          { LBRACKET (position lexbuf) }
  | "]"          { RBRACKET (position lexbuf) }
  | "{"          { LBRACE (position lexbuf) }
  | "}"          { RBRACE (position lexbuf) }
  | "_"          { UNDERSCORE (position lexbuf) }
  | "*"          { STAR (position lexbuf) }
  | [' ' '\t']   { token lexbuf }
  | '\n'         { incr_linenum lexbuf; token lexbuf}
  | _ as c       { printf "[Parse Error] Unrecognized character: %c\n" c; token lexbuf }
  | eof		       { EOF }

and comments level = parse
  | "*)"  { if level = 0 then token lexbuf else comments (level-1) lexbuf }
  | "(*"  { comments (level+1) lexbuf }
  | '\n'  { incr_linenum lexbuf; comments level lexbuf}
  | _     { comments level lexbuf }
  | eof   { raise End_of_file }
