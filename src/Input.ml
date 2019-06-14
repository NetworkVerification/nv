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
  | Failure x -> Console.error (Printf.sprintf "[Parser] %s" x)
  | End_of_file -> Console.error "[Parser] end of file in comment"
  | _ ->
    let tok, line, cnum = get_info () in
    let msg =
      Printf.sprintf "[Parser] token: %s, line: %s, char: %s" tok
        (string_of_int line) (string_of_int cnum)
    in
    Console.error msg

let read_from_in cin =
  let res = read (Lexing.from_channel cin) in
  close_in cin ; res

let read_from_str str = Lexing.from_string str |> read

let read_from_file fname =
  let cin = open_in fname in
  let res = read (Lexing.from_channel cin) in
  close_in cin ; res

(* Process include directives: return a list of filenames to be processesed
   in order. Do not include the same file more than once *)
let process_includes (fname : string) : string list =
  let rec process_includes_aux (seen, imports) fname =
    if List.mem fname seen then (seen, imports) else
      (* Get any imports in this file *)
      let lines = BatFile.lines_of fname in
      let includes = BatEnum.take_while (fun s -> BatString.starts_with s "include") lines in
      let imported_fnames = BatEnum.map (fun s ->
          if Str.string_match (Str.regexp "include[ ]*\\\"\\(.+\\)\\\"") s 0 then
            Str.matched_group 1 s
          else
            Console.error @@ "Bad include directive : " ^ s
        )
          includes
      in
      (* Recursively process those imports *)
      let rec_seen, rec_imports =
        BatEnum.fold process_includes_aux
          (fname::seen, imports) imported_fnames
      in
      (rec_seen, fname :: rec_imports)
  in
  let _, imports = process_includes_aux ([], []) fname in
  List.rev (fname :: imports)
;;

let parse fname =
  let t = Console.read_file fname in
  let ds = read_from_file fname in
  (ds, t)
