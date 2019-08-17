open Nv_lang.Syntax
open Nv_datastructures

let ty_mutator _ ty =
  match ty with
  | TEdge -> Some (TTuple [TNode; TNode])
  | _ -> None
;;

let pattern_mutator _ p _ =
  match p with
  | PEdge (p1, p2) -> Some (PTuple [p1; p2])
  | _ -> None
;;

let value_mutator _ v =
  let make_node n = avalue (vnode n, Some TNode, v.vspan) in
  match v.v with
  | VEdge (n1, n2) -> Some (vtuple [make_node n1; make_node n2])
  | _ -> None
;;

let exp_mutator _ _ = None;;

let map_back_mutator _ _ v orig_ty =
  match v.v, orig_ty with
  | VTuple [{v=VNode n1}; {v=VNode n2}], TEdge -> Some (vedge (n1, n2))
  | _ -> None
;;

(* The mask type for edges is always a tuple, even if we don't unbox them *)
let mask_mutator _ _ v _ = Some v;;

let make_toplevel (toplevel_mutator : 'a Mutators.toplevel_mutator) =
  toplevel_mutator ~name:"UnboxEdges" ty_mutator pattern_mutator value_mutator exp_mutator map_back_mutator mask_mutator
;;

let unbox_declarations = make_toplevel Mutators.mutate_declarations
let unbox_net = make_toplevel Mutators.mutate_network
let unbox_srp = make_toplevel Mutators.mutate_srp
