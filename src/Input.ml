open Console

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


let read_file fname : Console.info =
  let lines = ref [] in
  let indices = ref [] in
  let index = ref 0 in
  let chan =
    try open_in fname with _ ->
      Console.error (Printf.sprintf "file '%s' not found" fname)
  in
  try
    while true do
      let line = input_line chan in
      let len = String.length line in
      let new_len = !index + len + 1 in
      indices := (!index, new_len) :: !indices ;
      index := new_len ;
      lines := line :: !lines
    done ;
    {input= Array.of_list !lines; linenums= Array.of_list !indices}
  with End_of_file ->
    close_in chan ;
    { input= Array.of_list (List.rev !lines)
    ; linenums= Array.of_list (List.rev !indices) }


let parse fname =
  let t = read_file fname in
  let ds = read_from_file fname in
  (ds, t)
