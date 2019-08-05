open Batteries
open Nv_lang.Syntax
open Nv_lang.Collections
open Nv_utils.OCamlUtils
open Nv_solution
open Nv_datastructures.AdjGraph

(* Replace all instances of Unit with booleans (set to false), so we don't
   have to deal with them during SMT encoding *)
let rec unbox_ty ty =
  match ty with
  | TUnit -> TBool
  | TInt _ | TBool | TNode | TEdge -> ty
  | TOption ty -> TOption (unbox_ty ty)
  | TTuple tys -> TTuple (List.map unbox_ty tys)
  | TRecord map -> TRecord (StringMap.map unbox_ty map)
  | TMap (kty, vty) -> TMap (unbox_ty kty, unbox_ty vty)
  | TVar {contents = Link t} -> unbox_ty t
  | TArrow (ty1, ty2) -> TArrow (unbox_ty ty1, unbox_ty ty2)
  | TVar _ | QVar _ -> failwith "UnboxUnit.unbox_ty: bad type"
;;

let rec unbox_pat p =
  match p with
  | PUnit -> PBool false
  | PWild | PVar _ | PInt _ | PBool _ | POption None | PNode _ | PEdge _-> p
  | POption (Some p) -> POption (Some (unbox_pat p))
  | PTuple ps -> PTuple (List.map unbox_pat ps)
  | PRecord map -> PRecord (StringMap.map unbox_pat map)
;;

let rec unbox_val v =
  let v' =
    match v.v with
    | VUnit -> vbool false
    | VInt _ | VBool _ | VNode _| VEdge _ | VOption None -> v
    | VOption (Some v) -> voption (Some (unbox_val v))
    | VTuple vs -> vtuple (List.map unbox_val vs)
    | VRecord map -> vrecord (StringMap.map unbox_val map)
    | VMap _ -> failwith "TODO"
    | VClosure _ -> failwith "TODO"
  in
  avalue (v', omap unbox_ty v.vty, v.vspan)
;;

let rec unbox_exp e =
  let e' =
    match e.e with
    | EVal v -> e_val (unbox_val v)
    | EVar _ -> e
    | ETy (e, _) -> unbox_exp e
    | EOp (op, es) -> eop op (List.map unbox_exp es)
    | ESome e -> esome (unbox_exp e)
    | ETuple es -> etuple (List.map unbox_exp es)
    | ERecord map -> erecord (StringMap.map unbox_exp map)
    | EProject (e, l) -> eproject (unbox_exp e) l
    |EFun f -> efun
                 { f with
                   argty= Some (unbox_ty (oget f.argty));
                   resty= Some (unbox_ty (oget f.resty));
                   body= unbox_exp f.body }
    | EApp (e1, e2) -> eapp (unbox_exp e1) (unbox_exp e2)
    | ELet (x, e1, e2) -> elet x (unbox_exp e1) (unbox_exp e2)
    | EIf (test, e1, e2) -> eif (unbox_exp test) (unbox_exp e1) (unbox_exp e2)
    | EMatch (test, branches) -> ematch (unbox_exp test)
                                   (mapBranches (fun (p, b) -> (unbox_pat p, unbox_exp b)) branches)
  in
  aexp (e', omap unbox_ty e.ety, e.espan)
;;

let unbox_symbolic (x, toe) =
  let toe' =
    match toe with
    | Ty ty -> Ty (unbox_ty ty)
    | Exp e -> Exp (unbox_exp e)
  in
  x, toe'
;;

let unbox_decl d =
  match d with
  | DLet (x, tyo, e) -> DLet (x, omap unbox_ty tyo, unbox_exp e)
  | DInit e -> DInit (unbox_exp e)
  | DAssert e -> DAssert (unbox_exp e)
  | DTrans e -> DTrans (unbox_exp e)
  | DMerge e -> DMerge (unbox_exp e)
  | DSymbolic (x, toe) -> let (x, toe') = unbox_symbolic (x, toe) in DSymbolic (x, toe')
  | DRequire e -> DRequire (unbox_exp e)
  | DATy ty -> DATy (unbox_ty ty)
  | DUserTy (x, ty) -> DUserTy (x, unbox_ty ty)
  | DPartition e -> DPartition (unbox_exp e)
  | DInterface e -> DInterface (unbox_exp e)
  | DNodes _ | DEdges _ -> d
;;

let rec map_back_value v orig_ty =
  match v.v, orig_ty with
  | VBool false, TUnit -> vunit ()
  | (VBool _ | VInt _ | VNode _ | VEdge _ | VOption None | VUnit) , _ -> v
  | VOption (Some v'), TOption ty' -> voption (Some (map_back_value v' ty'))
  | VTuple vs, TTuple tys -> vtuple (List.map2 map_back_value vs tys)
  | VRecord vmap, TRecord tmap -> vrecord @@ StringMap.mapi (fun l v -> map_back_value v (StringMap.find l tmap)) vmap
  | VMap _, TMap _ -> failwith "TODO"
  | VClosure _, _ -> failwith "Can't have closures in atributes"
  | (VOption _ | VTuple _ | VRecord _ | VMap _), _ -> failwith "Type and value don't match"
;;

let map_back_sol symb_tys attr_ty (sol : Solution.t) : Solution.t =
  {
    symbolics = VarMap.mapi (fun x v -> map_back_value v (VarMap.find x symb_tys)) sol.symbolics;
    labels = VertexMap.map (fun v -> map_back_value v attr_ty) sol.labels;
    assertions = sol.assertions;
    mask = sol.mask (* Units and bools have the same mask type *)
  }
;;

let unbox_declarations ds =
  let attr_ty = get_attr_type ds |> oget in
  let symb_tys =
    get_symbolics ds
    |> List.fold_left
      (fun acc (x, toe) ->
         VarMap.add x (match toe with | Ty ty -> ty | Exp e -> (oget e.ety)) acc)
      VarMap.empty
  in
  List.map unbox_decl ds, map_back_sol symb_tys attr_ty
;;

let unbox_net (net : network) =
  let attr_ty = net.attr_type in
  let symb_tys =
    List.fold_left
      (fun acc (x, toe) ->
         VarMap.add x (match toe with | Ty ty -> ty | Exp e -> (oget e.ety)) acc)
      VarMap.empty
      net.symbolics
  in
  {
    attr_type = unbox_ty net.attr_type;
    init = unbox_exp net.init;
    trans = unbox_exp net.trans;
    merge = unbox_exp net.merge;
    assertion = omap unbox_exp net.assertion;
    symbolics = List.map unbox_symbolic net.symbolics;
    requires = List.map unbox_exp net.requires;
    utys = List.map (fun map -> StringMap.map unbox_ty map) net.utys;
    partition = omap unbox_exp net.partition;
    interface = omap unbox_exp net.interface;
    defs = List.map (fun (x, tyo, e) -> (x, omap unbox_ty tyo, unbox_exp e)) net.defs;
    graph = net.graph;
  },
  map_back_sol symb_tys attr_ty
