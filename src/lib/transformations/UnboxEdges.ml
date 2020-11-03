open Nv_lang.Syntax
open Nv_datastructures

let ty_transformer _ ty =
  match ty with
  | TEdge -> Some (TTuple [TNode; TNode])
  | _ -> None
;;

let pattern_transformer _ p _ =
  match p with
  | PEdge (p1, p2) -> Some (PTuple [p1; p2])
  | _ -> None
;;

let value_transformer _ v =
  let make_node n = avalue (vnode n, Some TNode, v.vspan) in
  match v.v with
  | VEdge (n1, n2) -> Some (vtuple [make_node n1; make_node n2])
  | _ -> None
;;

let exp_transformer _ _ = None

let map_back_transformer _ _ v orig_ty =
  match v.v, orig_ty with
  | VTuple [{ v = VNode n1 }; { v = VNode n2 }], TEdge -> Some (vedge (n1, n2))
  | VTuple [{ v = VInt n1 }; { v = VInt n2 }], TEdge ->
    Some (vedge (Integer.to_int n1, Integer.to_int n2))
  | _ -> None
;;

(* The mask type for edges is always a tuple, even if we don't unbox them *)
let mask_transformer _ _ v _ = Some v

let make_toplevel (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer
    ~name:"UnboxEdges"
    ty_transformer
    pattern_transformer
    value_transformer
    exp_transformer
    map_back_transformer
    mask_transformer
;;

let unbox_declarations = make_toplevel Transformers.transform_declarations
