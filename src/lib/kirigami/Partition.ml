open Batteries
open Nv_datastructures
open Nv_utils.PrimitiveCollections
open Nv_lang.Syntax
open TransformDecls
open Nv_interpreter

let is_cross_partition (f: AdjGraph.Vertex.t -> 'a) edge =
  (f (fst edge)) <> (f (snd edge))

(* It is possible that a better implementation involves building a new graph using the interface set,
 * as indexing newly-added nodes could break on AdjGraph implementation change
 *)
type onetwork =
  {
    attr_type       : ty;
    init            : exp;
    trans           : exp;
    merge           : exp;
    assertion       : exp option;
    symbolics       : (var * ty_or_exp) list;
    defs            : (var * ty option * exp) list;
    utys            : (var * ty) list;
    requires        : exp list;
    ograph          : OpenAdjGraph.t
  }

let partition_interface (partition: exp option) (interface: exp option) (graph: AdjGraph.t) : value option AdjGraph.EdgeMap.t =
  let open AdjGraph in
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

let open_network (net: network) : onetwork =
  let { attr_type; init; trans; merge; assertion; partition; interface; symbolics; defs; utys; requires; graph } : network = net
  in
  let ograph = OpenAdjGraph.from_graph graph in
  (* TODO: generate interface set, update ograph *)
  let part_int = partition_interface partition interface graph in
  {
    attr_type;
    init = transform_init init ograph ~intf:part_int; (*TODO: use actual hypotheses from InterfaceSet *)
    trans = transform_trans trans ograph;
    merge = transform_merge merge ograph;
    assertion;
    symbolics;
    defs;
    utys;
    requires;
    ograph;
  }
