
{
  open SMTParser
  open Printf

}

let id = ['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*
let symbol = ['~' '`' '!' '@' '#' '$' '%' '^' '&' '|' ':' '?' '>' '<' '[' ']' '=' '-' '.']+
let num = ['0'-'9']+
let tid = ['\'']['a'-'z' 'A'-'Z']['a'-'z' 'A'-'Z' '_' '0'-'9']*

rule token = parse
  | "false"      { FALSE }
  | "true"       { TRUE }
  | "mkUnit"     { UNIT }
  | "mkNone"     { NONE }
  | "mkSome"     { SOME }
  | "mkPair"num  { PAIR }
  | "as"         { AS }
  | num as n     { NUM (Nv_datatypes.Integer.of_string n) }
  | id as n      { ID n }
  | "("          { LPAREN }
  | ")"          { RPAREN }
  | "-"          { NEG    }
  | [' ' '\t']   { token lexbuf }
  | '\n'         { token lexbuf}
  | _ as c       { printf "[Parse Error] Unrecognized character: %c\n" c; token lexbuf }
  | eof		 { EOF }
