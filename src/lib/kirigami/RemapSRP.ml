open Nv_lang.Syntax
open Batteries
open SrpRemapping
open Nv_datastructures.AdjGraph
open Nv_transformations

let ty_transformer _ t = Some t

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

let remove_exps part_srp (recursors : Transformers.recursors) e =
  let removeExp = recursors.recurse_exp in
  let update_branches old_bs =
    foldBranches
      (fun (p, e) bs ->
        match p with
        | PEdge (PNode n1, PNode n2) ->
          let n1' = VertexMap.find_default None n1 part_srp.node_map in
          let n2' = VertexMap.find_default None n2 part_srp.node_map in
          (match n1', n2' with
          | Some u, Some v -> (PEdge (PNode u, PNode v), removeExp e) :: bs
          | _ -> bs)
        | PNode u ->
          (match VertexMap.find_default None u part_srp.node_map with
          | Some u' -> (PNode u', removeExp e) :: bs
          | None -> bs)
        | _ -> (p, removeExp e) :: bs)
      []
      old_bs
  in
  match e.e with
  | EMatch (e1, bs) ->
    let pat_exps = update_branches bs in
    (* put the branches back in the same order by going from the back *)
    let branches =
      List.fold_right (fun (p, e) b -> addBranch p e b) pat_exps emptyBranch
    in
    Some (ematch (removeExp e1) (optimizeBranches branches))
  | _ -> None
;;

let exp_transformer part_srp (recursors : Transformers.recursors) e =
  remove_exps part_srp recursors e
;;

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
    (exp_transformer part_srp)
    (map_back_transformer part_srp)
    mask_transformer
;;

let remap_declarations part_srp =
  make_toplevel part_srp Transformers.transform_declarations
;;
