open Nv_lang.Syntax
open Batteries
open Nv_kirigami.SrpRemapping
open Nv_datastructures.AdjGraph

(** Transformer utilities.
 ** This transformer impl remaps patterns and values to refer to the new node identities.
 ** However, it does not perform any action if the node found has been cut; we may in that
 ** case want to remove the entire offending expression or replace it with some default. *)

let ty_transformer _ ty = Some ty

let pattern_transformer (part_srp : partitioned_srp) (_ : Transformers.recursors) p t =
  match p, t with
  | PNode n, TNode ->
    let new_node = VertexMap.find_default None n part_srp.node_map in
    Option.map (fun n -> PNode n) new_node
  | PEdge (PNode n1, PNode n2), TEdge ->
    let new_edge = EdgeMap.find_default None (n1, n2) part_srp.edge_map in
    Option.map (fun (n1, n2) -> PEdge (PNode n1, PNode n2)) new_edge
  | _ -> None
;;

let value_transformer (part_srp : partitioned_srp) _ v =
  let make_node n = avalue (vnode n, Some TNode, v.vspan) in
  let make_edge e = avalue (vedge e, Some TEdge, v.vspan) in
  match v.v with
  | VNode n ->
    let new_node = VertexMap.find_default None n part_srp.node_map in
    Option.map (fun n -> make_node n) new_node
  | VEdge e ->
    let new_edge = EdgeMap.find_default None e part_srp.edge_map in
    Option.map (fun e -> make_edge e) new_edge
  | _ -> None
;;

let exp_transformer _ _ = None

let map_back_transformer (_part_srp : partitioned_srp) _ _ v _ =
  (* TODO: not yet implemented *)
  Some v
;;

(* not yet implemented *)
let mask_transformer _ _ v _ = Some v

let make_toplevel
    (part_srp : partitioned_srp)
    (toplevel_transformer : 'a Transformers.toplevel_transformer)
  =
  toplevel_transformer
    ~name:"RemapSrp"
    ty_transformer
    (pattern_transformer part_srp)
    (value_transformer part_srp)
    exp_transformer
    (map_back_transformer part_srp)
    mask_transformer
;;

let remap_declarations part_srp =
  make_toplevel part_srp Transformers.transform_declarations
;;
