open Batteries
open Cmdline
open Nv_lang
open Nv_lang.Syntax
open Nv_datastructures
open Partition
open Hijack

(** Remove all variable delimiters "~n" from the given string. *)
let strip_var_delims s =
  let regexp = Str.regexp "~[0-9]+\\b" in
  Str.global_replace regexp "" s
;;

let strip_sol_types s =
  let regexp = Str.regexp "solution<.*>" in
  Str.global_replace regexp "solution" s
;;

let clean_text = strip_var_delims % strip_sol_types

type fatLevel =
  | Core
  | Aggregation
  | Edge

type nodeGroup =
  | Fattree of fatLevel
  | Custom of string

let nodeGroup_of_string s =
  match s with
  | "core" -> Fattree Core
  | "aggregation" -> Fattree Aggregation
  | "edge" -> Fattree Edge
  | _ -> Custom s
;;

let string_of_nodeGroup g =
  match g with
  | Fattree Core -> "core"
  | Fattree Aggregation -> "aggregation"
  | Fattree Edge -> "edge"
  | Custom s -> s
;;

let parse_node_groups (fname : string) : (int, nodeGroup) Map.t =
  let lines =
    try File.lines_of fname with
    | _ -> Console.error ("File not found: " ^ fname)
  in
  let regexp = Str.regexp "\\([_a-zA-z0-9]+\\)\\(-[0-9]*\\)?=\\([0-9]+\\)" in
  (* aux fn to add nodes to a map with their associated group *)
  let rec collect_matches m line i =
    let offset =
      try Some (Str.search_forward regexp line i) with
      | Not_found -> None
    in
    match offset with
    | Some i ->
      let node = int_of_string (Str.matched_group 3 line) in
      let g = Str.matched_group 1 line in
      (* skip a pattern where the matched term isn't a group name but a record field *)
      (match g with
      | "lp" | "med" | "bgpAd" | "aslen" -> m
      | _ ->
        let group = nodeGroup_of_string g in
        let length = String.length (Str.matched_string line) in
        collect_matches (Map.add node group m) line (i + length))
    | None -> m
  in
  Enum.fold (fun m l -> collect_matches m l 0) Map.empty lines
;;

let nodeGroups_to_string (map : (int, nodeGroup) Map.t) : string =
  (* NOTE: we lose the indices associated with fattrees when we parse the groups,
   * but since we don't seem to need them this is hopefully OK *)
  let addGroup n g l = l @ [Printf.sprintf "%s=%d" (string_of_nodeGroup g) n] in
  let nodes = String.concat ", " (Map.foldi addGroup map []) in
  "(* {" ^ nodes ^ "} *)"
;;

type hijackStub =
  { leak : bool
  ; destination : int
  ; predicate : exp
  ; spines : int list
  }

type notransStub = { relationship : exp }

(* Change the given fattree network benchmark to model a hijack.
 * We add community tags to distinguish the legitimate destination
 * (provided by the hijackStub) from the hijacker (a newly-added node).
 * We add an assertion that routing goes towards the legitimate
 * destination as opposed to the hijacker, and wrap the original transferBgp
 * function with an additional community tag update.
 *)
let hijack decls hijackStub =
  let hijack_var = Var.fresh "hijack" in
  let new_node = get_nodes decls |> Option.get in
  let nspines = List.length hijackStub.spines in
  let new_edges =
    List.mapi (fun i u -> (u, new_node), i = nspines && hijackStub.leak) hijackStub.spines
    @ List.map (fun v -> (new_node, v), true) hijackStub.spines
  in
  let aty = get_attr_type decls |> Option.get in
  let update_decl d =
    match d with
    | DNodes n -> DNodes (n + 1)
    | DEdges es -> DEdges (es @ List.map fst new_edges)
    | DLet (v, oty, e) ->
      let e =
        match Var.name v with
        | "init" -> hijack_init new_node hijack_var e
        | "transferBgp" -> hijack_transferBgp new_edges e
        | "assert_node" -> hijack_assert_node new_node e
        | _ -> e
      in
      DLet (v, oty, e)
    | _ -> d
  in
  let decls = List.map update_decl decls in
  (* add the edgeTag declaration *)
  let edgeTag = hijack_edgetag new_node hijackStub.destination in
  (* add the hijack symbolic and hijack predicate *)
  let hijack_app =
    annot TBool (eapp hijackStub.predicate (annot aty (evar hijack_var)))
  in
  let hijack_decls = [DSymbolic (hijack_var, Ty aty); DRequire hijack_app] in
  (* return the hijacker node *)
  edgeTag :: (decls @ hijack_decls), new_node
;;

type genOp =
  | Cut of networkCut
  | Hijack of hijackStub
  | Notrans of notransStub

let main =
  let cfg, rest = argparse default "nvgen" Sys.argv in
  let file = rest.(0) in
  let op = rest.(1) in
  let write s =
    match cfg.outfile with
    | "-" -> IO.write_line IO.stdout s
    | file -> File.with_file_out file (fun out -> IO.write_line out s)
  in
  match op with
  | "hijack" ->
    if cfg.destination = -1 then failwith "No destination provided.";
    let predicate = predicate_to_exp cfg.predicate in
    let groups = parse_node_groups file in
    let spines =
      Map.foldi
        (fun u g l ->
          match g with
          | Fattree Core -> u :: l
          | _ -> l)
        groups
        []
    in
    let stub = { leak = cfg.leak; destination = cfg.destination; predicate; spines } in
    let decls, _ = Input.parse file in
    let new_ds, hijacker = hijack decls stub in
    let new_text = Printing.declarations_to_string new_ds in
    let cleaned = clean_text new_text in
    (* add the hijacker to the groups *)
    let groups = Map.add hijacker (Fattree Core) groups in
    let groupsComment = nodeGroups_to_string groups in
    write (cleaned ^ groupsComment)
  | _ -> ()
;;
