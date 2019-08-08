open Batteries
open Nv_lang
open Syntax
open Collections
open Nv_datastructures.AdjGraph
open Nv_utils.OCamlUtils
open Nv_solution

type 'a mutator = ('a -> 'a) -> 'a -> 'a option
type map_back_mutator = (value -> ty -> value) -> value -> ty -> value option
type mask_mutator = map_back_mutator

let rec mutate_ty
    ~(name:string)
    (ty_mutator : ty mutator) (ty : ty) =
  let mutate_ty = mutate_ty ~name:name ty_mutator in
  let ty_mutator = ty_mutator mutate_ty in
  match ty_mutator ty with
  | Some ty -> ty
  | None ->
    match ty with
    | TUnit | TBool | TInt _ | TNode | TEdge -> ty
    | TOption ty1 -> TOption (mutate_ty ty1)
    | TTuple tys -> TTuple (List.map mutate_ty tys)
    | TRecord map -> TRecord (StringMap.map mutate_ty map)
    | TArrow (ty1, ty2) -> TArrow (mutate_ty ty1, mutate_ty ty2)
    | TMap (kty, vty) -> TMap (mutate_ty kty, mutate_ty vty)
    | TVar {contents= Link ty1} -> mutate_ty ty1
    | TVar _ | QVar _ -> failwith @@ name ^ ": mutate_ty: encountered TVar or QVar"
;;

let rec mutate_pattern
    ~(name:string)
    (pat_mutator : pattern mutator) (p : pattern) =
  let mutate_pattern = mutate_pattern ~name:name pat_mutator in
  let pat_mutator = pat_mutator mutate_pattern in
  match pat_mutator p with
  | Some p -> p
  | None ->
    match p with
    | (PWild | PVar _ | PBool _ | PInt _ | PNode _ | PEdge _ | POption None | PUnit) -> p
    | POption (Some p) -> POption (Some (mutate_pattern p))
    | PTuple ps -> PTuple (List.map mutate_pattern ps)
    | PRecord pmap ->
      PRecord (StringMap.map mutate_pattern pmap)
;;

let rec mutate_value
    ~(name:string)
    (ty_mutator : ty mutator) (value_mutator : value mutator) (v : value) =
  let mutate_ty = mutate_ty ~name:name ty_mutator in
  let mutate_value = mutate_value ~name:name ty_mutator value_mutator in
  let value_mutator = value_mutator mutate_value in
  let v' =
    match value_mutator v with
    | Some v -> v
    | None ->
      match v.v with
      | VUnit | VInt _ | VBool _ | VNode _ | VEdge _ | VOption None -> v
      | VOption (Some v1) -> voption (Some (mutate_value v1))
      | VTuple vs -> vtuple (List.map mutate_value vs)
      | VRecord map -> vrecord (StringMap.map mutate_value map)
      | VMap bdd ->
        (* This op_key should be different on each call, and not used in the NV
           program. I think this value achieves that *)
        (* FIXME: Should this mutate key values as well? If so, the other bdd
           operations in this file should take that into account *)
        let op_key = e_val v, BatSet.PSet.empty in
        vmap (BddMap.map op_key (fun v -> mutate_value v) bdd)
      | VClosure _ -> failwith @@ name ^ ": mutate_value: encountered VClosure"
  in
  avalue (v', omap mutate_ty v.vty, v.vspan)
;;

let rec mutate_exp
    ~(name:string)
    (ty_mutator : ty mutator) (pat_mutator : pattern mutator) (value_mutator : value mutator)
    (exp_mutator : exp mutator) (e : exp) =
  let mutate_ty = mutate_ty ~name:name ty_mutator in
  let mutate_pattern = mutate_pattern ~name:name pat_mutator in
  let mutate_value = mutate_value ~name:name ty_mutator value_mutator in
  let mutate_exp = mutate_exp ~name:name ty_mutator pat_mutator value_mutator exp_mutator in
  let exp_mutator = exp_mutator mutate_exp in
  let e' =
    match exp_mutator e with
    | Some e -> e
    | None ->
      match e.e with
      | EVar _ -> e
      | EVal v -> e_val (mutate_value v)
      | ETy (e, ty) -> ety (mutate_exp e) (mutate_ty ty)
      | EOp (op, es) -> eop op (List.map mutate_exp es)
      | ESome e -> esome (mutate_exp e)
      | ETuple es -> etuple (List.map mutate_exp es)
      | ERecord map -> erecord (StringMap.map mutate_exp map)
      | EProject (e, l) -> eproject (mutate_exp e) l
      | EFun f -> efun
                    { f with
                      argty= Some (mutate_ty (oget f.argty));
                      resty= Some (mutate_ty (oget f.resty));
                      body= mutate_exp f.body }
      | EApp (e1, e2) -> eapp (mutate_exp e1) (mutate_exp e2)
      | ELet (x, e1, e2) -> elet x (mutate_exp e1) (mutate_exp e2)
      | EIf (test, e1, e2) -> eif (mutate_exp test) (mutate_exp e1) (mutate_exp e2)
      | EMatch (test, branches) -> ematch (mutate_exp test)
                                     (mapBranches (fun (p, b) -> (mutate_pattern p, mutate_exp b)) branches)
  in
  aexp (e', omap mutate_ty e.ety, e.espan)
;;

let mutate_symbolic
    ~(name:string)
    (ty_mutator : ty mutator) (pat_mutator : pattern mutator) (value_mutator : value mutator)
    (exp_mutator : exp mutator) (x, toe) =
  let toe' =
    match toe with
    | Ty ty -> Ty (mutate_ty ~name:name ty_mutator ty)
    | Exp e -> Exp (mutate_exp ~name:name ty_mutator pat_mutator value_mutator exp_mutator e)
  in
  x, toe'
;;

let mutate_decl
    ~(name:string)
    (ty_mutator : ty mutator) (pat_mutator : pattern mutator) (value_mutator : value mutator)
    (exp_mutator : exp mutator) (d : declaration) =
  let mutate_ty = mutate_ty ~name:name ty_mutator in
  let mutate_exp = mutate_exp ~name:name ty_mutator pat_mutator value_mutator exp_mutator in
  let mutate_symbolic = mutate_symbolic ~name:name ty_mutator pat_mutator value_mutator exp_mutator in
  match d with
  | DLet (x, tyo, e) -> DLet (x, omap mutate_ty tyo, mutate_exp e)
  | DInit e -> DInit (mutate_exp e)
  | DAssert e -> DAssert (mutate_exp e)
  | DTrans e -> DTrans (mutate_exp e)
  | DMerge e -> DMerge (mutate_exp e)
  | DSymbolic (x, toe) -> let (x, toe') = mutate_symbolic (x, toe) in DSymbolic (x, toe')
  | DRequire e -> DRequire (mutate_exp e)
  | DATy ty -> DATy (mutate_ty ty)
  | DUserTy (x, ty) -> DUserTy (x, mutate_ty ty)
  | DPartition e -> DPartition (mutate_exp e)
  | DInterface e -> DInterface (mutate_exp e)
  | DNodes _ | DEdges _ -> d
;;

let rec map_back_value
    ~(name:string)
    (map_back_mutator : map_back_mutator) (v : value) (orig_ty : ty) =
  let map_back_value = map_back_value ~name:name map_back_mutator in
  let map_back_mutator = map_back_mutator map_back_value in
  match map_back_mutator v orig_ty with
  | Some v -> v
  | None ->
    match v.v, orig_ty with
    | (VUnit | VBool _ | VInt _ | VNode _ | VEdge _ | VOption None), _ -> v
    | VOption (Some v'), TOption ty' -> voption (Some (map_back_value v' ty'))
    | VTuple vs, TTuple tys -> vtuple (List.map2 map_back_value vs tys)
    | VRecord vmap, TRecord tmap -> vrecord @@ StringMap.mapi (fun l v -> map_back_value v (StringMap.find l tmap)) vmap
    | VMap bdd, TMap (_, vty) ->
      let op_key = e_val v, BatSet.PSet.empty in
      vmap (BddMap.map op_key (fun v -> map_back_value v vty) bdd)
    | VClosure _, _ -> failwith @@ name ^ ": Can't have closures in attributes"
    | (VOption _ | VTuple _ | VRecord _ | VMap _), _ ->
      failwith @@
      Printf.sprintf "%s: map_back_value: value %s does not match type %s"
        name (Printing.value_to_string v) (Printing.ty_to_string orig_ty)
;;

let rec map_back_mask
    ~(name:string)
    (mask_mutator : mask_mutator) (v : value) (orig_ty : ty) =
  let map_back_mask = map_back_value ~name:name mask_mutator in
  let mask_mutator = mask_mutator map_back_mask in
  match mask_mutator v orig_ty with
  | Some v -> v
  | None ->
    match v.v, orig_ty with
    | VBool _, (TUnit | TBool | TInt _ | TNode)
    | VOption None, TOption _
      -> v
    | VOption (Some v), TOption ty -> voption (Some (map_back_mask v ty))
    | VTuple [v1; v2], TEdge -> vtuple [map_back_mask v1 TNode; map_back_mask v2 TNode]
    | VTuple vs, TTuple ts -> vtuple (List.map2 map_back_mask vs ts)
    | VRecord vmap, TRecord tmap -> vrecord @@ StringMap.mapi (fun l v -> map_back_mask v (StringMap.find l tmap)) vmap
    | VMap bdd, TMap (_, vty) ->
      let op_key = e_val v, BatSet.PSet.empty in
      vmap (BddMap.map op_key (fun v -> map_back_mask v vty) bdd)
    | (VUnit | VInt _ | VNode _ | VEdge _), _ ->
      failwith @@ name ^ ": Found illegal mask value"
    | VClosure _, _ ->
      failwith @@ name ^ ": Can't have closures in mask"
    | (VBool _ | VOption _ | VTuple _ | VRecord _ | VMap _) , _ ->
      failwith @@
      Printf.sprintf "%s: map_back_value: value %s does not match type %s"
        name (Printing.value_to_string v) (Printing.ty_to_string orig_ty)
;;

let map_back_sol
    ~(name:string)
    (map_back_mutator : map_back_mutator) (mask_mutator : mask_mutator) (symb_tys : ty VarMap.t)
    (attr_ty : ty) (sol : Solution.t)
  : Solution.t =
  let map_back_mask = (fun v -> map_back_mask ~name:name mask_mutator v attr_ty) in
  let map_back_value = map_back_value ~name:name map_back_mutator in
  {
    symbolics = VarMap.mapi (fun x v -> map_back_value v (VarMap.find x symb_tys)) sol.symbolics;
    labels = VertexMap.map (fun v -> map_back_value v attr_ty) sol.labels;
    assertions = sol.assertions; (* These mutations shouldn't change the truth value of the assertion *)
    mask = omap map_back_mask sol.mask;
  }
;;

let mutate_declarations
    ~(name:string)
    (ty_mutator : ty mutator) (pat_mutator : pattern mutator) (value_mutator : value mutator)
    (exp_mutator : exp mutator) (map_back_mutator : map_back_mutator) (mask_mutator : mask_mutator)
    (ds : declarations) =
  let attr_ty = get_attr_type ds |> oget in
  let symb_tys =
    get_symbolics ds
    |> List.fold_left
      (fun acc (x, toe) ->
         VarMap.add x (match toe with | Ty ty -> ty | Exp e -> (oget e.ety)) acc)
      VarMap.empty
  in
  List.map (mutate_decl ~name:name ty_mutator pat_mutator value_mutator exp_mutator) ds,
  map_back_sol ~name:name map_back_mutator mask_mutator symb_tys attr_ty
;;

let mutate_network
    ~(name:string)
    (ty_mutator : ty mutator) (pat_mutator : pattern mutator) (value_mutator : value mutator)
    (exp_mutator : exp mutator) (map_back_mutator : map_back_mutator) (mask_mutator : mask_mutator)
    (net : network) =
  let mutate_ty = mutate_ty ~name:name ty_mutator in
  let mutate_exp = mutate_exp ~name:name ty_mutator pat_mutator value_mutator exp_mutator in
  let mutate_symbolic = mutate_symbolic ~name:name ty_mutator pat_mutator value_mutator exp_mutator in
  let attr_ty = net.attr_type in
  let symb_tys =
    List.fold_left
      (fun acc (x, toe) ->
         VarMap.add x (match toe with | Ty ty -> ty | Exp e -> (oget e.ety)) acc)
      VarMap.empty
      net.symbolics
  in
  {
    attr_type = mutate_ty net.attr_type;
    init = mutate_exp net.init;
    trans = mutate_exp net.trans;
    merge = mutate_exp net.merge;
    assertion = omap mutate_exp net.assertion;
    symbolics = List.map mutate_symbolic net.symbolics;
    requires = List.map mutate_exp net.requires;
    utys = List.map (fun map -> StringMap.map mutate_ty map) net.utys;
    partition = omap mutate_exp net.partition;
    interface = omap mutate_exp net.interface;
    defs = List.map (fun (x, tyo, e) -> (x, omap mutate_ty tyo, mutate_exp e)) net.defs;
    graph = net.graph;
  },
  map_back_sol ~name:name map_back_mutator mask_mutator symb_tys attr_ty
