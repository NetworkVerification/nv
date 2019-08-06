(* Replaces all 0-element tuples in the program with unit,
   and all 1-element tuples with their only element. For now,
   assumes maps have already been unrolled *)

open Nv_lang
open Syntax
open Nv_utils.OCamlUtils
open Nv_solution

let mapo f o =
  match o with
  | None -> None
  | Some x -> Some (f x)
;;

let rec cleanup_ty ty =
  match ty with
  | TUnit | TBool | TInt _ | TNode | TEdge | QVar _ -> ty
  | TTuple [] -> TUnit
  | TTuple [ty'] -> cleanup_ty ty'
  | TTuple tys -> TTuple (List.map cleanup_ty tys)
  | TArrow (ty1, ty2) -> TArrow (cleanup_ty ty1, cleanup_ty ty2)
  | TOption ty' -> TOption (cleanup_ty ty')
  | TVar r ->
    begin
      match !r with
      | Link t -> cleanup_ty t
      | Unbound _ -> ty
    end
  | TMap _ | TRecord _ -> failwith "Should be unrolled"
;;

let rec cleanup_pattern p =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PVar _ | PNode _ | PEdge _ -> p
  | PTuple [] -> PUnit
  | PTuple [p] -> cleanup_pattern p
  | PTuple ps -> PTuple (List.map cleanup_pattern ps)
  | POption po -> POption (mapo cleanup_pattern po)
  | PRecord _ -> failwith "Should be unrolled"
;;

let rec cleanup_val v =
  let new_v =
    match v.v with
    | VUnit | VBool _ | VInt _ | VNode _ | VEdge _ -> v
    | VTuple [] -> vunit ()
    | VTuple [v'] -> cleanup_val v'
    | VTuple vs -> vtuple (List.map cleanup_val vs)
    | VOption vo -> voption (mapo cleanup_val vo)
    | VRecord _ | VMap _ -> failwith "Should be unrolled"
    | VClosure _ -> failwith "Should be inlined"
  in
  avalue (new_v, mapo cleanup_ty v.vty, v.vspan)
;;

let rec cleanup_exp e =
  let new_e =
    match e.e with
    | ETuple [] -> e_val (vunit ())
    | ETuple [e] -> cleanup_exp e
    | ETuple es -> etuple (List.map cleanup_exp es)
    | EVar _ -> e
    | EOp (op, es) ->
      begin
        match op, es with
        | TGet (size, _, _), [e1] ->
          if size = 0 then e_val (avalue (vunit (), Some TUnit, e1.espan))
          else if size = 1 then cleanup_exp e1
          else eop op (List.map cleanup_exp es)
        | TSet (size, _, _), [e1; e2] ->
          if size = 0 then e_val (avalue (vunit (), Some TUnit, e1.espan))
          else if size = 1 then cleanup_exp e2
          else eop op (List.map cleanup_exp es)
        | (TGet _ | TSet _), _ -> failwith "Bad TGet/TSet"
        | _ -> e (* No other ops take tuples as arguments, so no need to recurse *)
      end
    | ETy (e, ty) -> ety (cleanup_exp e) (cleanup_ty ty)
    | EVal v -> e_val (cleanup_val v)
    | ESome e -> esome (cleanup_exp e)
    | EApp (e1, e2) -> eapp (cleanup_exp e1) (cleanup_exp e2)
    | EFun f -> efun { f with
                       argty= mapo cleanup_ty f.argty;
                       resty= mapo cleanup_ty f.resty;
                       body= cleanup_exp f.body }
    | EIf (e1, e2, e3) -> eif (cleanup_exp e1) (cleanup_exp e2) (cleanup_exp e3)
    | ELet (x, e1, e2) -> elet x (cleanup_exp e1) (cleanup_exp e2)
    | EMatch (e, branches) -> ematch (cleanup_exp e)
                                (mapBranches (fun (p, e) -> (cleanup_pattern p, cleanup_exp e)) branches)
    | ERecord _ | EProject _ -> failwith "Should be unrolled"
  in
  aexp (new_e, mapo cleanup_ty e.ety, e.espan)
;;

let cleanup_toe toe =
  match toe with
  | Ty ty -> Ty (cleanup_ty ty)
  | Exp e -> Exp (cleanup_exp e)
;;

let rec cleanup_decl d =
  match d with
  | DNodes _ | DEdges _ -> d
  | DInit e -> DInit (cleanup_exp e)
  | DTrans e -> DTrans (cleanup_exp e)
  | DMerge e -> DMerge (cleanup_exp e)
  | DAssert e -> DAssert (cleanup_exp e)
  | DLet (x, tyo, e) -> DLet (x, mapo cleanup_ty tyo, cleanup_exp e)
  | DSymbolic (x, toe) -> DSymbolic(x, cleanup_toe toe)
  | DRequire e -> DRequire (cleanup_exp e)
  | DATy aty -> DATy (cleanup_ty aty)
  | DUserTy (x, ty) -> DUserTy (x, cleanup_ty ty)
  | _ -> failwith "not yet implemented!"
;;

let rec cleanup_net_aux (n : Syntax.network) : Syntax.network =
  {
    attr_type = cleanup_ty n.attr_type;
    init = cleanup_exp n.init;
    trans = cleanup_exp n.trans;
    merge = cleanup_exp n.merge;
    assertion = omap cleanup_exp n.assertion;
    partition = omap cleanup_exp n.partition;
    interface = omap cleanup_exp n.interface;
    symbolics = List.map (fun (v, toe) -> (v, cleanup_toe toe)) n.symbolics;
    defs = List.map (fun (v,tyo,e) -> (v, omap cleanup_ty tyo, cleanup_exp e)) n.defs;
    utys = List.map (fun map -> match cleanup_ty (TRecord map) with | TRecord map -> map | _ -> failwith "impossible") n.utys;
    requires = List.map cleanup_exp n.requires;
    graph = n.graph;
  }
;;

(** Functions to convert a solution to the cleanupd version to a solution
    to the original version **)

let rec map_back_value v oldty =
  let uncleanupd_v =
    match v.v, oldty with
    | VUnit, TUnit
    | VBool _, TBool
    | VInt _, TInt _ -> v
    | _, TTuple [] -> vtuple []
    | _, TTuple [ty] -> vtuple [map_back_value v ty]
    | VTuple tys, TTuple oldtys -> vtuple (List.map2 map_back_value tys oldtys)
    | VOption vo, TOption ty -> voption (mapo (fun vo -> map_back_value vo ty) vo)
    | VRecord _, _ | VMap _, _ | VClosure _, _ -> failwith "Should be unrolled"
    | _ -> failwith @@ Printf.sprintf "Type and value do not match: (%s, %s)"
        (Printing.value_to_string v) (Printing.ty_to_string oldty)
  in
  avalue (uncleanupd_v, Some oldty, v.vspan)
;;

let map_back_symbolics symbolics (sol : Nv_solution.Solution.t) =
  let symbolics_to_convert =
    BatList.filter_map
      (fun (v, e) ->
         let oldty = match e with Syntax.Ty ty -> ty | Exp e -> Nv_utils.OCamlUtils.oget e.ety in
         let newty = cleanup_ty oldty in
         if Typing.equiv_tys oldty newty then None
         else Some (v, oldty))
      symbolics
  in
  let convert_symbolic var v =
    let symb =
      List.find_opt
        (fun (var', _) -> Nv_datastructures.Var.equal var var')
        symbolics_to_convert
    in
    match symb with
    | None -> v
    | Some(_, original_ty) ->
      map_back_value v original_ty
  in
  let new_symbolics =
    Collections.VarMap.mapi convert_symbolic sol.symbolics
  in
  new_symbolics

let map_back_attrs attr_ty (sol : Nv_solution.Solution.t) =
  Nv_datastructures.AdjGraph.VertexMap.map
    (fun v -> map_back_value v attr_ty)
    sol.labels
;;

let map_back symbolics attr_ty (sol : Nv_solution.Solution.t) =
  {sol with
   symbolics = map_back_symbolics symbolics sol;
   labels = map_back_attrs attr_ty sol;
   mask = omap (fun v -> map_back_value v (Solution.mask_type_ty attr_ty)) sol.mask
  }
;;

let cleanup_declarations decls =
  let symbolics = Syntax.get_symbolics decls in
  let attr_ty = Nv_utils.OCamlUtils.oget (Syntax.get_attr_type decls) in
  (List.map cleanup_decl decls, map_back symbolics attr_ty)

let cleanup_net net =
  (cleanup_net_aux net, map_back net.symbolics net.attr_type)
