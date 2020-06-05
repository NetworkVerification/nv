open Batteries
open Nv_lang
open Syntax
open Collections
open Nv_datastructures.AdjGraph
open Nv_utils.OCamlUtils
open Nv_solution

type recursors = {
  recurse_ty: ty -> ty;
  recurse_pattern: pattern -> ty -> pattern;
  recurse_value: value -> value;
  recurse_exp: exp -> exp;
}

type 'a transformer = recursors -> 'a -> 'a option
type pattern_transformer = recursors -> pattern -> ty -> pattern option
type map_back_transformer = (value -> ty -> value) -> Solution.t -> value -> ty -> value option
type mask_transformer = map_back_transformer

type 'a toplevel_transformer =
  name:string ->
  ty transformer ->
  pattern_transformer ->
  value transformer ->
  exp transformer ->
  map_back_transformer ->
  mask_transformer ->
  'a ->
  'a * Solution.map_back

type transformers = {
  ty_transformer: ty transformer;
  pattern_transformer: pattern_transformer;
  value_transformer: value transformer;
  exp_transformer: exp transformer;
}

let rec build_recursors ~(name:string) (transformers:transformers) : recursors =
  {
    recurse_ty = transform_ty ~name:name transformers;
    recurse_pattern = transform_pattern ~name:name transformers;
    recurse_value = transform_value ~name:name transformers;
    recurse_exp = transform_exp ~name:name transformers;
  }

and transform_ty ~(name:string) (transformers:transformers) (ty : ty) : ty =
  let recursors = build_recursors ~name:name transformers in
  let transform_ty = recursors.recurse_ty in
  let ty_transformer = transformers.ty_transformer recursors in
  match ty_transformer ty with
  | Some ty -> ty
  | None ->
    match ty with
    | TUnit | TBool | TInt _ | TNode | TEdge -> ty
    | TOption ty1 -> TOption (transform_ty ty1)
    | TTuple tys -> TTuple (List.map transform_ty tys)
    | TRecord map -> TRecord (StringMap.map transform_ty map)
    | TArrow (ty1, ty2) -> TArrow (transform_ty ty1, transform_ty ty2)
    | TMap (kty, vty) -> TMap (transform_ty kty, transform_ty vty)
    | TVar {contents= Link ty1} -> transform_ty ty1
    | TVar _ | QVar _ -> failwith @@ name ^ ": transform_ty: encountered TVar or QVar"

and transform_pattern ~(name:string) (transformers:transformers) (p : pattern) (ty : ty) : pattern =
  let ty = get_inner_type ty in (* FIXME: This should be handled somewhere else, ideally in Typing.ml *)
  let recursors = build_recursors ~name:name transformers in
  let transform_pattern = recursors.recurse_pattern in
  let pat_transformer = transformers.pattern_transformer recursors in
  match pat_transformer p ty with
  | Some p -> p
  | None ->
    match p, ty with
    | (PWild | PVar _), _
    | PUnit, TUnit
    | PBool _, TBool
    | PInt _, TInt _
    | PNode _, TNode
    | PEdge _, TEdge
    | POption None, TOption _ -> p
    | POption (Some p), TOption ty -> POption (Some (transform_pattern p ty))
    | PTuple ps, TTuple tys -> PTuple (List.map2 transform_pattern ps tys)
    | PRecord pmap, TRecord tmap ->
      PRecord (StringMap.mapi (fun l p -> transform_pattern p (StringMap.find l tmap)) pmap)
    | _, _ -> failwith @@ Printf.sprintf "%s: transform_pattern: pattern %s does not match type %s\n"
        name (Printing.pattern_to_string p) (Printing.ty_to_string ty)

and transform_value ~(name:string) (transformers:transformers) (v : value) : value =
  let recursors = build_recursors ~name:name transformers in
  let transform_ty, transform_value = recursors.recurse_ty, recursors.recurse_value in
  let value_transformer = transformers.value_transformer recursors in
  let v' =
    match value_transformer v with
    | Some v -> v
    | None ->
      match v.v with
      | VUnit | VInt _ | VBool _ | VNode _ | VEdge _ | VOption None -> v
      | VOption (Some v1) -> voption (Some (transform_value v1))
      | VTuple vs -> vtuple (List.map transform_value vs)
      | VRecord map -> vrecord (StringMap.map transform_value map)
      | VMap bdd ->
        (* This op_key should be different on each call, and not used in the NV
           program. I think this value achieves that *)
        (* FIXME: Should this transform key values as well? If so, the other bdd
           operations in this file should take that into account *)
        let op_key = e_val v, BatSet.PSet.empty in
        vmap (BddMap.map op_key (fun v -> transform_value v) bdd)
      | VClosure _ -> failwith @@ name ^ ": transform_value: encountered VClosure"
  in
  avalue (v', omap transform_ty v.vty, v.vspan)

and transform_exp ~(name:string) (transformers:transformers) (e : exp) : exp =
  let recursors = build_recursors ~name:name transformers in
  let transform_ty, transform_pattern, transform_value, transform_exp =
    recursors.recurse_ty, recursors.recurse_pattern, recursors.recurse_value, recursors.recurse_exp
  in
  let exp_transformer = transformers.exp_transformer recursors in
  let e' =
    match exp_transformer e with
    | Some e -> e
    | None ->
      match e.e with
      | EVar _ -> e
      | EVal v -> e_val (transform_value v)
      | ETy (e, ty) -> ety (transform_exp e) (transform_ty ty)
      | EOp (op, es) -> eop op (List.map transform_exp es)
      | ESome e -> esome (transform_exp e)
      | ETuple es -> etuple (List.map transform_exp es)
      | ERecord map -> erecord (StringMap.map transform_exp map)
      | EProject (e, l) -> eproject (transform_exp e) l
      | EFun f -> efun
                    { f with
                      argty= Some (transform_ty (oget f.argty));
                      resty= Some (transform_ty (oget f.resty));
                      body= transform_exp f.body }
      | EApp (e1, e2) -> eapp (transform_exp e1) (transform_exp e2)
      | ELet (x, e1, e2) -> elet x (transform_exp e1) (transform_exp e2)
      | EIf (test, e1, e2) -> eif (transform_exp test) (transform_exp e1) (transform_exp e2)
      | EMatch (test, branches) ->
        ematch (transform_exp test)
          (mapBranches (fun (p, b) -> (transform_pattern p (oget test.ety), transform_exp b)) branches)
  in
  aexp (e', omap transform_ty e.ety, e.espan)
;;

let transform_symbolic ~(name:string) (transformers:transformers) (x, toe) =
  let toe' =
    match toe with
    | Ty ty -> Ty (transform_ty ~name:name transformers ty)
    | Exp e -> Exp (transform_exp ~name:name transformers e)
  in
  x, toe'
;;

let transform_decl ~(name:string) (transformers:transformers) (d : declaration) =
  let transform_ty = transform_ty ~name:name transformers in
  let transform_exp = transform_exp ~name:name transformers in
  let transform_symbolic = transform_symbolic ~name:name transformers in
  match d with
  | DLet (x, tyo, e) -> DLet (x, omap transform_ty tyo, transform_exp e)
  | DAssert e -> DAssert (transform_exp e)
  | DSolve {aty; var_names; init; trans; merge} ->
    let var_names, init, trans, merge =
      transform_exp var_names, transform_exp init, transform_exp trans, transform_exp merge
    in
    DSolve {aty = omap transform_ty aty; var_names; init; trans; merge}
  | DSymbolic (x, toe) -> let (x, toe') = transform_symbolic (x, toe) in DSymbolic (x, toe')
  | DRequire e -> DRequire (transform_exp e)
  | DUserTy (x, ty) -> DUserTy (x, transform_ty ty)
  | DPartition e -> DPartition (transform_exp e)
  | DInterface e -> DInterface (transform_exp e)
  | DNodes _ | DEdges _ -> d
;;

let rec map_back_value
    ~(name:string)
    (sol : Solution.t) (map_back_transformer : map_back_transformer) (v : value) (orig_ty : ty) =
  let map_back_value = map_back_value ~name:name sol map_back_transformer in
  let map_back_transformer = map_back_transformer map_back_value sol in
  let orig_ty = get_inner_type orig_ty in
  match map_back_transformer v orig_ty with
  | Some v -> v
  | None ->
    match v.v, orig_ty with
    | (VUnit | VBool _ | VInt _ | VNode _ | VEdge _ | VOption None), _ -> v
    | VOption (Some v'), TOption ty' -> voption (Some (map_back_value v' ty'))
    | VTuple vs, TTuple tys -> vtuple (List.map2 map_back_value vs tys)
    | VRecord vmap, TRecord tmap -> vrecord @@ StringMap.mapi (fun l v -> map_back_value v (StringMap.find l tmap)) vmap
    | VMap bdd, TMap (kty, vty) ->
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
    (sol : Solution.t) (mask_transformer : mask_transformer) (v : value) (orig_ty : ty) =
  let map_back_mask = map_back_value ~name:name sol mask_transformer in
  let mask_transformer = mask_transformer map_back_mask sol in
  let orig_ty = get_inner_type orig_ty in
  match mask_transformer v orig_ty with
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

(* NOTE: I don't think solve_tys is necessary or the right way to go here. We
   should store the original type at each transformation pass *)
let map_back_sol
    ~(name:string)
    (map_back_transformer : map_back_transformer) (mask_transformer : mask_transformer) (symb_tys : ty VarMap.t)
    (solve_tys : ty VarMap.t) (sol : Solution.t)
  : Solution.t =
  let map_back_mask = map_back_mask ~name:name sol mask_transformer in
  let map_back_value = map_back_value ~name:name sol map_back_transformer in
  let solves =
    List.map
      (fun (v,{Solution.sol_val; mask}) ->
         let aty = VarMap.find v solve_tys in
         (v, {Solution.sol_val = map_back_value sol_val aty;
              mask = omap (fun v -> map_back_mask v aty) mask;
              attr_ty = aty}))
      sol.solves
  in
  {
    symbolics = List.map (fun (x,v) ->
        try (x, map_back_value v (VarMap.find x symb_tys))
        with | Not_found -> (x,v)) sol.symbolics;
    assertions = sol.assertions; (* These transformations shouldn't change the truth value of the assertion *)
    solves = solves;
    nodes = sol.nodes;
  }
;;

let get_symbolic_types symbs =
  List.fold_left
    (fun acc (x, toe) ->
       VarMap.add x (match toe with | Ty ty -> ty | Exp e -> (oget e.ety)) acc)
    VarMap.empty
    symbs
;;

let get_solve_types solves =
  let rec add_tys acc e =
    match e.e with
    | EVar x -> VarMap.add x (oget e.ety) acc
    | ETuple es -> List.fold_left add_tys acc es
    | _ -> failwith "Bad DSolve"
  in
  List.fold_left (fun acc s -> add_tys acc s.var_names) VarMap.empty solves
;;

let transform_declarations
    ~(name:string)
    (ty_transformer : ty transformer) (pattern_transformer : pattern_transformer) (value_transformer : value transformer)
    (exp_transformer : exp transformer) (map_back_transformer : map_back_transformer) (mask_transformer : mask_transformer)
    (ds : declarations) =
  let symb_tys = get_symbolics ds |> get_symbolic_types in
  let solve_tys = get_solves ds |> get_solve_types in
  let transformers = {ty_transformer; pattern_transformer; value_transformer; exp_transformer} in
  List.map (transform_decl ~name:name transformers) ds,
  map_back_sol ~name:name map_back_transformer mask_transformer symb_tys solve_tys
;;
