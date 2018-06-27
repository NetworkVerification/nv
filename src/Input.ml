let read lexbuf =
  let get_info () =
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    let tok = Lexing.lexeme lexbuf in
    (tok, line, cnum)
  in
  try Parser.prog Lexer.token lexbuf with
  | Parsing.Parse_error ->
      let tok, line, cnum = get_info () in
      Printf.printf "[Parse Error] token: %s, line: %s, char: %s\n" tok
        (string_of_int line) (string_of_int cnum) ;
      exit 0
  | Failure x ->
      Printf.printf "[Parse Error] %s\n" x ;
      exit 0
  | End_of_file ->
      Printf.printf "[Parse Error] end of file in comment\n" ;
      exit 0


let read_from_in cin =
  let res = read (Lexing.from_channel cin) in
  close_in cin ; res


let read_from_str str = Lexing.from_string str |> read

let read_from_file fname =
  let cin = open_in fname in
  let res = read (Lexing.from_channel cin) in
  close_in cin ; res
