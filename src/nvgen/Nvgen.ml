(** A utility program to generate NV files.
 *  Can be used to generate one file from another (extending a policy),
 *  or to create stub topologies.
 *)
open Batteries
open Cmdline
open Nv_lang.Syntax
open Nv_lang.Input
open Nv_datastructures
open Partition
open Hijack
open Maintenance
open FaultTolerance
open Utils
open Topologies

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

(** Return a declaration of a destination node. *)
let dest_decl d =
  DLet (Var.fresh "dest", None, e_val (vnode d))

type nodeGroup =
  | Fat of Topologies.fatLevel
  | Custom of string

let nodeGroup_of_string s =
  match s with
  | "core" -> Fat Core
  | "aggregation" -> Fat Aggregation
  | "edge" -> Fat Edge
  | _ -> Custom s
;;

let string_of_nodeGroup g =
  match g with
  | Fat Core -> "core"
  | Fat Aggregation -> "aggregation"
  | Fat Edge -> "edge"
  | Custom s -> s
;;

let parse_node_groups (fname : string) : (int, nodeGroup) Map.t =
  let lines =
    try File.lines_of fname with
    | _ -> Nv_lang.Console.error ("File not found: " ^ fname)
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
        | "trans" -> hijack_trans e
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
  let nti = node_to_int_decl (new_node + 1) in
  let hijack_decls =
    [nti; edgeTag; DSymbolic (hijack_var, Ty aty); DRequire hijack_app]
  in
  (* return the hijacker node *)
  decls @ hijack_decls, new_node
;;

let maintenance dest decls =
  let down_var = Var.fresh "down" in
  let aty = get_attr_type decls |> Option.get in
  let update_decl d =
    match d with
    | DLet (v, oty, e) ->
      let e =
        match Var.name v with
        | "trans" -> maintenance_trans aty e
        | "transferBgp" -> maintenance_transferBgp e
        | "assert_node" -> maintenance_assert_node e
        | _ -> e
      in
      DLet (v, oty, e)
    | _ -> d
  in
  let decls = List.map update_decl decls in
  let tagDown = tagDown_decl down_var in
  let dest_not_down =
    eop Not [eop Eq [evar down_var; e_val (voption (Some (vint (Integer.of_int dest))))]]
  in
  let nodes = get_nodes decls |> Option.get in
  let new_decls =
    [ node_to_int_decl nodes
    ; tagDown
    ; DSymbolic (down_var, Ty (TOption (TInt 32)))
    ; DRequire dest_not_down ]
  in
  decls @ new_decls
;;

let fault_tolerance nfaults decls =
  (* for each fault, construct a failure variable *)
  let fail_vars =
    List.map
      (fun i -> Var.fresh (Printf.sprintf "failed%d" i))
      (Nv_utils.OCamlUtils.list_seq nfaults)
  in
  (* add a drop condition to the transfer *)
  let update_decl d =
    match d with
    | DLet (v, oty, e) ->
      let e =
        match Var.name v with
        | "trans" -> ft_trans e
        | _ -> e
      in
      DLet (v, oty, e)
    | _ -> d
  in
  let decls = List.map update_decl decls in
  let edges = get_edges decls |> Option.get in
  (* construct a symbolic for each failure *)
  let fail_symbolics =
    List.map
      (fun var -> DSymbolic (var, Ty (TOption (TTuple [TInt 32; TInt 32]))))
      fail_vars
  in
  let new_decls = [edge_to_int_pair_decl edges; isFailed_decl fail_vars] in
  decls @ new_decls @ fail_symbolics
;;

let main =
  let cfg, rest = argparse default "nvgen" Sys.argv in
  let file = rest.(0) in
  let op = rest.(1) in
  let new_ds, groups =
    match op, cfg.destination with
    | "topology", d ->
      let decls, _ = parse file in
      let topology = Option.bind cfg.topology Topologies.parse_string in
      let topology_decls = match topology with
      | None -> failwith "Invalid topology given (should be a 'star', 'ring' or 'mesh' followed by an integer)."
      | Some top -> Topologies.to_decls (Topologies.construct top) in
      (* add a destination, if provided *)
      let decls = if d != -1 then (dest_decl d) :: decls else decls in
      decls @ topology_decls, Map.empty
    | "ft", _ ->
      let decls, _ = parse file in
      let new_ds = fault_tolerance cfg.nfaults decls in
      new_ds, parse_node_groups file
    | _, -1 -> failwith "No destination provided."
    | "hijack", destination ->
      let predicate = predicate_to_exp cfg.predicate in
      let groups = parse_node_groups file in
      let spines =
        Map.foldi
          (fun u g l ->
            match g with
            | Fat Core -> u :: l
            | _ -> l)
          groups
          []
      in
      let stub = { leak = cfg.leak; destination; predicate; spines } in
      let decls, _ = parse file in
      let new_ds, hijacker = hijack decls stub in
      (* add the hijacker to the groups *)
      new_ds, Map.add hijacker (Fat Core) groups
    | "maintenance", dest ->
      let decls, _ = parse file in
      let new_ds = maintenance dest decls in
      new_ds, parse_node_groups file
    | _ -> failwith ("invalid op: " ^ op)
  in
  let new_text = Nv_lang.Printing.declarations_to_string new_ds in
  let cleaned = clean_text new_text in
  let groupsComment = nodeGroups_to_string groups in
  let output = cleaned ^ groupsComment in
  match cfg.outfile with
  | "-" -> IO.write_line IO.stdout output
  | f -> File.with_file_out f (fun out -> IO.write_line out output)
;;
