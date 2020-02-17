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

(** Representation of a cut edge with an associated hypothesis and a predicate on that hypothesis *)
type cut_edge =
  { u: Vertex.t;
    v: Vertex.t;
    h: var;
    p: exp;
  }

(** Helper function to extract the edge predicate
 *  from the interface expression.
 *)
let interp_interface intfe e : exp option = 
  let intf_app = Interp.apply empty_env (deconstructFun intfe) (vedge e) in
    (* if intf_app is not an option, or if the value it contains is not a function,
     * fail *)
  match intf_app with
  | {v = VOption o; _} -> begin match o with
    | Some {v = VClosure (_env, func); _ } -> Some (efunc func)
    | Some _ -> failwith "expected a closure, got something else instead!"
    (* infer case *)
    | None -> None
    end
  | _ -> failwith "intf value is not an option; did you type check the input?"

(** Helper function to extract the partition index
 *  from the partition expression.
 *)
let interp_partition parte node : int =
  let value = Interp.apply empty_env (deconstructFun parte) (vnode node)
  in (int_of_val value) |> Option.get

(* Generate a map of edges to annotations from the given partition and interface expressions
 * and a list of edges.
 * If the interface is absent, use None for each value.
 * @return a map from edges in the original SRP to associated values
 *)
let map_edges_to_interface (partition: exp option) (interface: exp option) (edges: edge list) : exp option EdgeMap.t =
  match partition with
  | Some parte -> begin
      let get_edge_hyp map e = 
        (* Add each cross-partition edge to the interface *)
        if (is_cross_partition (interp_partition parte) e) then
          let intf_pred = match interface with
          | Some intfe -> interp_interface intfe e
          | None -> None
          in
          EdgeMap.add e intf_pred map
        else
          map
      in
      List.fold_left get_edge_hyp EdgeMap.empty edges
  end
  | None -> EdgeMap.empty

(** Helper function to unwrap the predicate. *)
let unwrap_pred maybe_pred = match maybe_pred with
| Some pred -> pred (* the interface is an efun *)
| None -> e_val (vbool true)

(** Create a symbolic variable for each cut edge.
 *  This function maps each edge's optional predicate
 *  into a pair: a hypothesis variable and a predicate we can
 *  apply to that hypothesis variable.
 *  @return a map from edges to hypothesis and predicate information *)
let create_hyp_vars (interface: exp option EdgeMap.t) : (var * exp) EdgeMap.t =
  let create_hyp_pred edge maybe_pred =
    (* generate the var *)
    let name = Printf.sprintf "hyp_%s" (Edge.to_string edge) in
    (Var.fresh name, unwrap_pred maybe_pred)
  in
  EdgeMap.mapi create_hyp_pred interface

(* FIXME: this code is currently broken by the changes to interfaces *)
let open_network (net: network) : network =
  let { attr_type; init; trans; merge; assertion; partition; interface; symbolics; defs; utys; requires; graph } : network = net
  in
  let part_int = map_edges_to_interface partition interface (fold_edges_e List.cons graph []) in
  let edge_hyps = create_hyp_vars part_int in
  (* map of edges to expressions using the hypotheses (for use in init) *)
  let _input_exps = EdgeMap.map (fun (var, _pred) -> evar var) edge_hyps in
  let _output_preds = EdgeMap.map (fun (_var, pred) -> pred) edge_hyps in
  (* pass in set of edges to partitioner *)
  let edges = EdgeMap.fold (fun k _ s -> EdgeSet.add k s) part_int EdgeSet.empty in
  let (graph, _interfaces) = OpenAdjGraph.partition_graph graph (OpenAdjGraph.intf_empty) edges in
  {
    attr_type;
    init = init; (* FIXME: transform_init init interfaces input_exps; *)
    trans = trans; (* FIXME: transform_trans trans interfaces; *)
    merge; (* = transform_merge merge interfaces; *)
    partition = None;
    interface = None;
    assertion = assertion; (* FIXME: transform_assert assertion interfaces output_preds; *)
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
let partition_edge (nodes: int) (edges: edge list) (e: edge)
  ({outputs; inputs; outs_broken; broken_ins}: OpenAdjGraph.interfaces_alt) 
  : (int * edge list * OpenAdjGraph.interfaces_alt) 
=
  let (u,v) = e in
  let (outnode, innode) = (nodes, nodes + 1) in
  let parted_edges = [(u, outnode); (innode, v)] in
  let new_nodes = nodes + 2 in
  let new_edges = (List.remove edges e) @ parted_edges in
  let new_intf : OpenAdjGraph.interfaces_alt = {
    inputs = VertexMap.add innode v inputs;
    outputs = VertexMap.add outnode u outputs;
    outs_broken = VertexMap.add outnode e outs_broken;
    broken_ins = EdgeMap.add e innode broken_ins;
  } in
  (new_nodes, new_edges, new_intf)

(** Create a new map from the given map of cut edges to hypothesis-predicate pairs,
 *  where each key is an input~base edge, and each value is an expression using the hypothesis.
 *  This is then used to add the input cases to the init function.
 *)
let get_input_exps ({ broken_ins; _}: OpenAdjGraph.interfaces_alt) (edge_hyps: (var * exp) EdgeMap.t) : (exp EdgeMap.t) =
  (* create an edgemap of input~base keys to hypothesis expression values *)
  let add_edge_to_hyp (u, v) inn m =
    let (var, _) = EdgeMap.find (u,v) edge_hyps in
    EdgeMap.add (inn,v) (evar var) m
  in
  EdgeMap.fold add_edge_to_hyp broken_ins EdgeMap.empty

(** Create a list of lists of declarations representing a network which has been
 * opened along the edges described by the partition and interface declarations.
 * @return a new list of lists of declarations
 *)
let divide_decls (decls: declarations) : declarations list =
  let partition = get_partition decls in
  match partition with
  | Some parte -> begin
    let attr_type = get_attr_type decls |> Option.get in
    (* get the parameters for partition_edges *)
    let interface = get_interface decls in
    let nodes = get_nodes decls |> Option.get in
    let edges = get_edges decls |> Option.get in
    let partf : (Vertex.t -> int) = interp_partition parte in
    let intf_opt : (Edge.t -> exp option) = 
      match interface with
        | Some intfe -> (interp_interface intfe)
        | None -> fun (_: Edge.t) -> None
    in
    let interfacef = unwrap_pred % intf_opt in
    let node_list = List.range 0 `To (nodes - 1) in
    let partitioned_srps = SrpRemapping.partition_edges node_list edges partf interfacef in
    let create_new_decls parted_srp : declarations =
      (* TODO: the node_map and edge_map describe how to remap each node and edge in the new SRP.
       * To transform more cleanly, we can run a toplevel transformer on the SRP, replacing
       * each edge and node in the map with the new value if it's Some, and removing it if it's None
       * (where the edge/node is explicitly used).
       * We can then add code to handle adding in the new input and output nodes to the SRP.
       * (the input and output edges are handled by edge_map).
       *)
      let { nodes; edges; node_map; edge_map; intf; preds; } : SrpRemapping.partitioned_srp = parted_srp in
      (* filter all predicate edges out that do not appear in the given vertex->vertex map *)
      let filter_preds vmap =
        EdgeMap.filter (fun (u, v) _ -> begin
          (* match on both binding arrangements, since outputs go output~base but preds goes base~output *)
          (* there's no risk of mismatching, since outputs and inputs all have only one neighbour *)
          let is_pred_in_vmap u' v' = (u' = u && v' = v ) || (u' = v && v' = u) in
            VertexMap.exists is_pred_in_vmap vmap
        end) preds
      in
      let edge_hyps = EdgeMap.mapi (fun edge p -> begin
        let name = Printf.sprintf "hyp_%s" (Edge.to_string edge) in
        (Var.fresh name, p)
      end) (filter_preds intf.inputs) in
      let output_preds = filter_preds intf.outputs in
      let input_exps = EdgeMap.map (fun (v, _) -> (evar v)) edge_hyps in
      (* TODO: remap decls using node_map and edge_map *)
      let trans = get_trans decls |> Option.get in
      let new_trans = transform_trans trans intf edge_map in
      let init = get_init decls |> Option.get in
      let new_init = transform_init init intf input_exps node_map in
      let merge = get_merge decls |> Option.get in
      let new_merge = transform_merge merge intf node_map in
      let new_symbolics = EdgeMap.fold (fun _ (v, _) l -> DSymbolic (v, Ty attr_type) :: l) edge_hyps [] in
      let assertion = get_assert decls in
      let new_assertion = transform_assert assertion intf output_preds node_map in
      let new_requires = EdgeMap.fold (fun _ (v, p) l -> DRequire (eapp p (evar v)) :: l) edge_hyps [] in
      (* replace relevant old decls *)
      let new_decls = List.filter_map (fun d -> match d with
      | DNodes _ -> Some (DNodes nodes)
      | DEdges _ -> Some (DEdges edges)
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
    in
    List.map create_new_decls partitioned_srps
  end
  | None -> [decls]
