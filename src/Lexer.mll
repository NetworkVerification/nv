
{
  open Parser
  open Printf
  exception Eof

  let incr_linenum lexbuf =
    let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- 
      { pos with Lexing.pos_lnum = pos.Lexing.pos_lnum + 1; 
                 Lexing.pos_bol = pos.Lexing.pos_cnum; } ;;

}

let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*
let symbol = ['~' '`' '!' '@' '#' '$' '%' '^' '&' '|' ':' '?' '>' '<' '[' ']' '=' '-' '.']+
let num = ['0'-'9']+
  
rule token = parse
  | "(*"         { comments 0 lexbuf }
  | "false"      { FALSE }
  | "true"       { TRUE }
  | "let"        { LET }
  | "in"         { IN }
  | "if"         { IF }
  | "then"       { THEN }
  | "else"       { ELSE }
  | "fun"        { FUN }
  | "None"       { NONE }
  | "Some"       { SOME }
  | "edges"      { EDGES }
  | "nodes"      { NODES }
  | "match"      { MATCH }
  | "with"       { WITH }
  | "default"    { DEFAULT }
  | id as s      { ID (Var.create s) }
  | num as n     { NUM (Unsigned.UInt32.of_string n) }
  | "&&"         { AND }
  | "||"         { OR }
  | "|"          { BAR }
  | "->"         { ARROW }
  | "!"          { NOT }
  | "."          { DOT }
  | ","          { COMMA }
  | "+"          { PLUS }
  | "-"          { SUB }
  | "="          { EQ }
  | "<"          { LESS }
  | ">"          { GREATER }
  | ";"          { SEMI }
  | "("          { LPAREN }
  | ")"          { RPAREN }
  | "["          { LBRACKET }
  | "]"          { RBRACKET }
  | "{"          { LBRACE }
  | "}"          { RBRACE }
  | "_"          { UNDERSCORE }
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
