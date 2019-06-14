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

(* Make dest_fname relative to the current directory (or absolute),
   instead of relative to the source_fname *)
let adjust_filename source_fname dest_fname =
  dest_fname
  |> FilePath.concat (FilePath.dirname source_fname)
  |> FilePath.reduce ~no_symlink:true
;;

(* Process include directives: return a list of filenames to be processesed
   in order. Do not include the same file more than once *)
let process_includes (fname : string) : string list =
  let rec process_includes_aux (seen, imports) fname =
    if List.mem fname seen then (seen, imports) else
      (* Get any imports in this file *)
      let lines =
        try BatFile.lines_of fname
        with _ -> Console.error ("File not found: " ^ fname)
      in
      let includes =
        BatEnum.take_while
          (fun s -> BatString.starts_with s "include")
          (BatEnum.filter (fun s -> String.trim s <> "") lines)
      in
      let imported_fnames = BatEnum.map (fun s ->
          if Str.string_match (Str.regexp "include[ ]*\\\"\\(.+\\)\\\"") s 0 then
            adjust_filename fname (Str.matched_group 1 s)
          else
            Console.error @@ "Bad include directive (did you forget the quotes?): " ^ s
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
  let _, imports = process_includes_aux ([], []) (adjust_filename FilePath.current_dir fname) in
  List.rev imports
;;

let parse fname =
  let files_to_parse = process_includes fname in
  let t = Console.read_files files_to_parse in
  let ds = List.concat (List.map read_from_file files_to_parse) in
  (ds, t)
