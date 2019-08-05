open Nv_lang.Syntax

let ty_mutator _ ty =
  match ty with
  | TEdge -> Some (TTuple [TNode; TNode])
  | _ -> None
;;

let pat_mutator _ p =
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

let map_back_mutator _ v orig_ty =
  match v.v, orig_ty with
  | VTuple [{v=VNode n1}; {v=VNode n2}], TEdge -> Some (vedge (n1, n2))
  | _ -> None
;;

(* Pretty sure this works *)
let mask_mutator = map_back_mutator;;

let unbox_declarations = Mutators.mutate_declarations ty_mutator pat_mutator value_mutator exp_mutator map_back_mutator mask_mutator;;
let unbox_net = Mutators.mutate_network ty_mutator pat_mutator value_mutator exp_mutator map_back_mutator mask_mutator;;
