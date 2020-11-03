open Batteries

let read ?(filename : string option = None) lexbuf =
  let get_info () =
    let curr = lexbuf.Lexing.lex_curr_p in
    let line = curr.Lexing.pos_lnum in
    let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
    let tok = Lexing.lexeme lexbuf in
    tok, line, cnum
  in
  let err_header =
    match filename with
    | None -> "[Parser]"
    | Some s -> Printf.sprintf "[Parser] %s:" s
  in
  try Parser.prog Lexer.token lexbuf with
  | Failure x -> Console.error (Printf.sprintf "%s %s" err_header x)
  | End_of_file -> Console.error (Printf.sprintf "%s end of file in comment" err_header)
  | _ ->
    let tok, line, cnum = get_info () in
    let msg =
      Printf.sprintf
        "%s token: %s, line: %s, char: %s"
        err_header
        tok
        (string_of_int line)
        (string_of_int cnum)
    in
    Console.error msg
;;

let read_from_in cin =
  let res = read (Lexing.from_channel cin) in
  close_in cin;
  res
;;

let read_from_str str = Lexing.from_string str |> read

let read_from_file fname =
  let fin = open_in fname in
  let lexbuf = Lexing.from_channel fin in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = fname };
  lexbuf.lex_start_p <- { lexbuf.lex_start_p with pos_fname = fname };
  let res = read ~filename:(Some fname) lexbuf in
  close_in fin;
  res
;;

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
    print_endline @@ "Processing " ^ fname;
    if List.mem fname seen
    then seen, imports
    else (
      (* Get any imports in this file *)
      let lines =
        try File.lines_of fname with
        | _ -> Console.error ("File not found: " ^ fname)
      in
      let includes =
        Enum.take_while
          (fun s -> String.starts_with s "include")
          (Enum.filter
             (fun s -> (not @@ String.starts_with s "(*") && String.trim s <> "")
             lines)
      in
      let imported_fnames =
        Enum.map
          (fun s ->
            if Str.string_match (Str.regexp "include[ ]*\\\"\\(.+\\)\\\"") s 0
            then adjust_filename fname (Str.matched_group 1 s)
            else
              Console.error @@ "Bad include directive (did you forget the quotes?): " ^ s)
          includes
      in
      (* Recursively process those imports *)
      let rec_seen, rec_imports =
        Enum.fold process_includes_aux (fname :: seen, imports) imported_fnames
      in
      rec_seen, fname :: rec_imports)
  in
  let _, imports =
    process_includes_aux ([], []) (adjust_filename FilePath.current_dir fname)
  in
  List.rev imports
;;

module DeclG = Graph.Persistent.Digraph.Concrete(struct
    type t = Syntax.declaration
    let compare = Pervasives.compare
    let equal = (fun a b -> compare a b = 0)
    let hash = Hashtbl.hash
  end)

module DeclSort = Graph.Topological.Make(DeclG)

(** Compute two maps:
  * - the map from each declaration to the list of variables it depends on.
  * - the map from each variable to the declaration it references.
  * We can then combine these maps to get a map from each declaration
  * to the list of declarations it depends on.
*)
let get_decl_vars (var_m, decl_m) d =
  let open Syntax in
  let extend_map_list k newv m = Map.modify_opt k (fun oldv -> match oldv with
      | Some old -> Some (newv @ old)
      | None -> Some (newv)) m
  in
  match d with
  | DLet (v, _, e) -> let vars = get_exp_vars e in
    (extend_map_list d vars var_m, Map.add v d decl_m)
  | DSymbolic (v, t_or_e) -> let deps = match t_or_e with
      | Ty t -> (get_ty_vars t)
      | Exp e -> (get_exp_vars e)
    in (extend_map_list d deps var_m, Map.add v d decl_m)
  | DUserTy (v, t) -> let deps = get_ty_vars t in
    (extend_map_list d deps var_m, Map.add v d decl_m)
  | DAssert e -> (extend_map_list d (get_exp_vars e) var_m, decl_m)
  | DRequire e -> (extend_map_list d (get_exp_vars e) var_m, decl_m)
  | DPartition e -> (extend_map_list d (get_exp_vars e) var_m, decl_m)
  | DSolve {aty; var_names; init; trans; merge; interface} -> begin
      let ty_vars = match aty with
        | Some t -> (get_ty_vars t)
        | None -> [] in
      let interface_vars = match interface with
        | Some i -> (get_exp_vars i)
        | None -> [] in
      (extend_map_list d (ty_vars @
                          (get_exp_vars var_names) @
                          (get_exp_vars init) @
                          (get_exp_vars trans) @
                          (get_exp_vars merge) @ interface_vars) var_m, decl_m)
    end
  (* DNodes and DEdges *)
  | _ -> (extend_map_list d [] var_m, decl_m)

let sort_decls ds =
  let open Syntax in
  let open Nv_datastructures.AdjGraph in
  (* Add a dependency from k to each decl in decls in g;
   * we add k to the graph as well in case it has no dependencies *)
  let add_dep k decls g = List.fold_left (fun g v -> DeclG.add_edge g k v) (DeclG.add_vertex g k) decls in
  (* Ordering:
   * - Sort the user-defined types
   * - Sort the symbolics based on which depends on another
   * - Sort the let bindings based on which depends on another
   * - Add links from the let bindings to all other declarations
  *)
  let (decl_to_vars, var_to_decl) = List.fold_left get_decl_vars (Map.empty, Map.empty) ds in
  let map_vars_to_decls vars : declaration list =
    (* if a variable is not in var_to_decls, we just ignore it,
     * as it's probably initialized inside the declaration itself *)
    List.filter_map (fun v -> Map.Exceptionless.find v var_to_decl) vars
  in
  let decl_to_decls = Map.map map_vars_to_decls decl_to_vars in
  let dep_graph : DeclG.t = Map.foldi add_dep decl_to_decls DeclG.empty in
  (* return the newly sorted declarations *)
  DeclSort.fold List.cons dep_graph []

let parse fname =
  let files_to_parse = process_includes fname in
  let t = Console.read_files files_to_parse in
  let old_ds = List.concat (List.map read_from_file files_to_parse) in
  (* print_endline @@ Printing.declarations_to_string ds; *) 
  let ds = sort_decls old_ds in
  (* check that the lists have equal length *)
  assert (List.compare_lengths old_ds ds = 0);
  ds, t
;;
