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
 * Fail if the valye is not an option.
 *)
let proj_opt (v: value) : value option =
  match v with
  | {v = VOption o; _ } -> o
  | _ -> failwith "value is not an option"

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
            (* if intf_app is not an option, fail *)
            EdgeMap.add (u, v) (proj_opt intf_app) map
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
let create_hyp_vars attr_type (interface: value option EdgeMap.t) : (var * exp) EdgeMap.t =
  let create_hyp_var edge = 
    let name = Printf.sprintf "hyp_%s" (Edge.to_string edge) in
    Var.fresh name
  in
  let create_hyp_pred edge maybe_value =
    let h = create_hyp_var edge in
    (* generate a predicate; if there is no specific value given, set it to true *)
    let p = match maybe_value with
    | Some v -> create_exact_predicate attr_type v
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
  let (graph, interfaces) = OpenAdjGraph.partition_graph graph (OpenAdjGraph.intf_empty) EdgeSet.empty in
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
