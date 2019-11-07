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

let partition_interface (partition: exp option) (interface: exp option) (graph: AdjGraph.t) : value option EdgeMap.t =
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
            EdgeMap.add (u, v) (Some intf_app) map
          else
            map
        in
        fold_edges get_edge_hyp graph EdgeMap.empty
    (* Mark every edge as to be inferred *)
    | None -> fold_edges (fun u v m -> EdgeMap.add (u, v) None m) graph EdgeMap.empty
  end
  | None -> EdgeMap.empty

(** Create a symbolic variable for each cut edge.
 *  @return a map from edges to hypothesis and predicate information *)
let create_hyp_vars (interface: value option EdgeMap.t) : (var * exp) EdgeMap.t =
  let create_hyp_var edge = 
    let name = Printf.sprintf "hyp_%s" (Edge.to_string edge) in
    Var.fresh name
  in
  let create_predicate var value =
    eop Eq [(evar var); (e_val value)]
  in
  let create_hyp_pred edge maybe_value =
    let h = create_hyp_var edge in
    (* generate a predicate; if there is no specific value given, set it to true *)
    let p = match maybe_value with
    | Some v -> create_predicate h v
    | None -> e_val (vbool true)
  in (h, p)
  in
  EdgeMap.mapi create_hyp_pred interface

let open_network (net: network) : network =
  let { attr_type; init; trans; merge; assertion; partition; interface; symbolics; defs; utys; requires; graph } : network = net
  in
  let part_int = partition_interface partition interface graph in
  let edge_hyps = create_hyp_vars part_int in
  (* map of edges to expressions using the hypotheses (for use in init) *)
  let input_exps = EdgeMap.map (fun (var, _pred) -> evar var) edge_hyps in
  let (graph, interfaces) = OpenAdjGraph.partition_graph graph (OpenAdjGraph.intf_empty) EdgeSet.empty in
  (* TODO: use interface information to add assert/require constraints using new symbolic variables *)
  {
    attr_type;
    init = transform_init init interfaces input_exps;
    trans = transform_trans trans interfaces;
    merge = transform_merge merge interfaces;
    partition = None;
    interface = None;
    assertion = transform_assert assertion interfaces; (* TODO *)
    symbolics = EdgeMap.fold (fun _k (v, _) l -> (v, Ty attr_type) :: l) edge_hyps symbolics;
    defs;
    utys;
    requires = EdgeMap.fold (fun _k (_, p) l -> p :: l) edge_hyps requires;
    graph;
  }
