open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Nv_utils.PrimitiveCollections
open Nv_lang.Syntax
open TransformDecls
open Nv_interpreter

let is_cross_partition (f: Vertex.t -> 'a) edge =
  (f (fst edge)) <> (f (snd edge))

(* It is possible that a better implementation involves building a new graph using the interface set,
 * as indexing newly-added nodes could break on AdjGraph implementation change
 *)
type onetwork =
  {
    network         : network;
    interfaces      : OpenAdjGraph.interfaces;
  }

(** Representation of a cut edge with an associated hypothesis and a predicate on that hypothesis *)
type cut_edge =
  { u: Vertex.t;
    v: Vertex.t;
    h: var;
    p: exp;
  }

(** Transform a value representing an option into an optional value.
 * Fail if the value is not an option.
 *)
let proj_opt (v: value) : value option =
  match v with
  | {v = VOption o; _ } -> o
  | _ -> failwith "value is not an option"

(** Extract the closure value of the interface and
 * convert it to a simple expression of a function.
 *)
let extract_intf_closure (value: value) : exp =
  match value.v with
  | VClosure (_env, func) -> efunc func
  | _ -> failwith "intf value was not a closure"

(* Generate a map of edges to annotations from the given partition and interface expressions
 * and a list of edges.
 * @return a map from edges in the original SRP to associated values
 *)
let partition_interface_edges (partition: exp option) (interface: exp option) (edges: edge list) : exp option EdgeMap.t =
  match partition with
  | Some parte -> begin
    match interface with
    (* Add each cross-partition edge to the interface *)
    | Some intfe -> 
        let get_edge_hyp map e = 
          (* partition testing function *)
          let partf_app node = Interp.apply empty_env (deconstructFun parte) (vnode node) in
          (* interface hypothesis *)
          let intf_app = Interp.apply empty_env (deconstructFun intfe) (vedge e) in
          if (is_cross_partition partf_app e) then
            (* if intf_app is not an option, fail *)
            let intf_pred = (proj_opt intf_app) |> Option.map extract_intf_closure in
            EdgeMap.add e intf_pred map
          else
            map
        in
        List.fold_left get_edge_hyp EdgeMap.empty edges
    (* Mark every edge as to be inferred *)
    | None -> List.fold_left (fun m e -> EdgeMap.add e None m) EdgeMap.empty edges
  end
  | None -> EdgeMap.empty

let partition_interface (partition: exp option) (interface: exp option) (graph: AdjGraph.t) : exp option EdgeMap.t =
  match partition with
  | Some parte -> begin
    match interface with
    (* Add each cross-partition edge to the interface *)
    | Some intfe -> 
        let get_edge_hyp u v map = 
          (* partition testing function *)
          let partf_app node = Interp.apply empty_env (deconstructFun parte) (vnode node) in
          (* interface hypothesis *)
          let intf_app = Interp.apply empty_env (deconstructFun intfe) (vedge (u, v)) in
          if (is_cross_partition partf_app (u, v)) then
            (* if intf_app is not an option, fail *)
            let intf_pred = (proj_opt intf_app) |> Option.map extract_intf_closure in
            EdgeMap.add (u, v) intf_pred map
          else
            map
        in
        fold_edges get_edge_hyp graph EdgeMap.empty
    (* Mark every edge as to be inferred *)
    | None -> fold_edges (fun u v m -> EdgeMap.add (u, v) None m) graph EdgeMap.empty
  end
  | None -> EdgeMap.empty

(** Return a function representing a predicate over attributes,
 * which compares a given variable to an exact value.
 *)
let create_exact_predicate attr_type value =
  let var = Var.fresh "x" in
  let body = eop Eq [(evar var); (e_val value)] in
    efunc (funcFull var (Some attr_type) (Some TBool) body)

(** Create a symbolic variable for each cut edge.
 *  @return a map from edges to hypothesis and predicate information *)
let create_hyp_vars _attr_type (interface: exp option EdgeMap.t) : (var * exp) EdgeMap.t =
  let create_hyp_var edge = 
    let name = Printf.sprintf "hyp_%s" (Edge.to_string edge) in
    Var.fresh name
  in
  let create_hyp_pred edge maybe_pred =
    let h = create_hyp_var edge in
    (* generate a predicate; if there is no specific value given, set it to true *)
    let p = match maybe_pred with
    | Some pred -> pred (* the interface is an efun *)
    | None -> e_val (vbool true)
    in (h, p)
  in
  EdgeMap.mapi create_hyp_pred interface

let open_network (net: network) : network =
  let { attr_type; init; trans; merge; assertion; partition; interface; symbolics; defs; utys; requires; graph } : network = net
  in
  let part_int = partition_interface partition interface graph in
  let edge_hyps = create_hyp_vars attr_type part_int in
  (* map of edges to expressions using the hypotheses (for use in init) *)
  let input_exps = EdgeMap.map (fun (var, _pred) -> evar var) edge_hyps in
  let output_preds = EdgeMap.map (fun (_var, pred) -> pred) edge_hyps in
  (* pass in set of edges to partitioner *)
  let edges = EdgeMap.fold (fun k _ s -> EdgeSet.add k s) part_int EdgeSet.empty in
  let (graph, interfaces) = OpenAdjGraph.partition_graph graph (OpenAdjGraph.intf_empty) edges in
  {
    attr_type;
    init = transform_init init interfaces input_exps;
    trans = transform_trans trans interfaces;
    merge; (* = transform_merge merge interfaces; *)
    partition = None;
    interface = None;
    assertion = transform_assert assertion interfaces output_preds;
    symbolics = EdgeMap.fold (fun _k (v, _) l -> (v, Ty attr_type) :: l) edge_hyps symbolics;
    defs;
    utys;
    (* add requires clauses for each hypothesis, applying the predicate to the hypothesis variable *)
    requires = EdgeMap.fold (fun _k (v, p) l -> (eapp p (evar v)) :: l) edge_hyps requires;
    graph;
  }

(* Return a new version of the nodes and edges where edge e has been replaced
 * by an output-input pair.
 *)
let partition_edge (nodes: int) (edges: edge list) (e: edge) (intf: OpenAdjGraph.interfaces) : (int * edge list * OpenAdjGraph.interfaces) =
  let (u,v) = e in
  let (outnode, innode) = (nodes, nodes + 1) in
  let parted_edges = [(u, outnode); (innode, v)] in
  let new_nodes = nodes + 2 in
  let new_edges = (List.remove edges e) @ parted_edges in
  let new_intf = OpenAdjGraph.{
    inputs = VertexMap.add innode v intf.inputs;
    outputs = VertexMap.add outnode u intf.outputs;
    broken = VertexMap.add outnode innode intf.broken;
  } in
  (new_nodes, new_edges, new_intf)

let get_input_exps (interfaces: OpenAdjGraph.interfaces) (edge_hyps: (var * exp) EdgeMap.t) : (exp EdgeMap.t) =
  let OpenAdjGraph.{ outputs; inputs; broken } = interfaces in
  let find_old_edge outn inn =
    let u = VertexMap.find outn outputs in
    let v = VertexMap.find inn inputs in
    (u, v)
  in
  (* create an edgemap of input~base keys to hypothesis expression values *)
  VertexMap.fold (fun (outn: Vertex.t) (inn: Vertex.t) m -> 
    let (u,v) = find_old_edge outn inn in
    let (var, _) = EdgeMap.find (u,v) edge_hyps in
    EdgeMap.add (inn,v) (evar var) m) broken EdgeMap.empty

let open_declarations (decls: declarations) : declarations =
  let open Nv_transformations in
  let partition = get_partition decls in
  if Option.is_some partition then
    let attr_type = get_attr_type decls |> Option.get in
    let interface = get_interface decls in
    let nodes = get_nodes decls |> Option.get in
    let edges = get_edges decls |> Option.get in
    let part_int = partition_interface_edges partition interface edges in
    let edge_hyps = create_hyp_vars attr_type part_int in
    let output_preds = EdgeMap.map (fun (_var, pred) -> pred) edge_hyps in
    let (new_nodes, new_edges, intf) = EdgeMap.fold (fun e _ (n, es, i) -> begin
      partition_edge n es e i
    end) part_int (nodes, edges, OpenAdjGraph.intf_empty) in
    let input_exps = get_input_exps intf edge_hyps in
    let trans = get_trans decls |> Option.get in
    let new_trans = transform_trans trans intf in
    let init = get_init decls |> Option.get in
    let new_init = transform_init init intf input_exps in
    let merge = get_merge decls |> Option.get in
    let new_merge = transform_merge merge intf in
    let new_symbolics = EdgeMap.fold (fun _ (v, _) l -> DSymbolic (v, Ty attr_type) :: l) edge_hyps [] in
    let assertion = get_assert decls in
    let new_assertion = transform_assert assertion intf output_preds in
    let new_requires = EdgeMap.fold (fun _ (v, p) l -> DRequire (eapp p (evar v)) :: l) edge_hyps [] in
    (* replace relevant old decls *)
    let new_decls = List.filter_map (fun d -> match d with
    | DNodes _ -> Some (DNodes new_nodes)
    | DEdges _ -> Some (DEdges new_edges)
    | DInit _ -> Some (DInit new_init)
    | DTrans _ -> Some (DTrans new_trans)
    (* FIXME: merge is screwy; currently an output node on the destination won't update since it
     * gets initialized with the destination's value, which is already the best *)
    | DMerge _ -> Some (DMerge new_merge)
    | DAssert _ -> Some (DAssert (Option.get new_assertion))
    (* remove partition and interface declarations *)
    | DPartition _ -> None
    | DInterface _ -> None
    | _ -> Some d) decls in
    (* add the assertion in at the end if there wasn't an assert in the original decls *)
    let add_assert = if Option.is_none assertion then [DAssert (Option.get new_assertion)] else [] in
    (* also add requires at the end so they can use any bindings earlier in the file *)
    new_symbolics @ new_decls @ new_requires @ add_assert
  else
    (* no partition provided; do nothing *)
    decls
