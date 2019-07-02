open Syntax
open Collections
open Typing

let has_target_type (target : ty) (e : exp) : bool =
  match e.ety with
  | Some (ty) ->
    equiv_tys target ty
  | None ->
    failwith "Found expression with no ety during map unrolling"
;;

let get_index keys k =
  try
    let index, _ =
      BatList.findi (fun _ e -> compare_es e k = 0) keys
    in
    Some(index)
  with
  | _ -> None
;;

let mapo f o =
  match o with
  | None -> None
  | Some x -> Some (f x)
;;

let rec unroll_type
    (ty : ty)
    (keys : exp list)
    (ty2 : ty)
  : ty
  =
  let unroll_type = unroll_type ty keys in
  match (canonicalize_type ty2) with
  | TUnit
  | TBool
  | TInt _
  | TNode
  | TEdge ->
    ty2
  | TArrow (t1, t2) ->
    TArrow (unroll_type t1, unroll_type t2)
  | TTuple tys ->
    TTuple (BatList.map unroll_type tys)
  | TOption ty ->
    TOption (unroll_type ty)
  | TMap (key_ty, val_ty) ->
    if equiv_tys ty ty2 then
      (* Don't need to recurse since types cannot contain themselves *)
      TTuple (BatList.make (BatList.length keys) (canonicalize_type val_ty))
    else
      TMap (unroll_type key_ty, unroll_type val_ty)
  | TRecord map -> TRecord (StringMap.map unroll_type map)
  | QVar tyname -> QVar tyname
  (* failwith "Cannot unroll a type containing a QVar!"; *)
  | TVar _ ->
    failwith "Encountered TVar after canonicalization"
;;

let rec unroll_exp
    (ty : ty)
    (keys : exp list)
    (e : exp)
  : exp
  =
  let unroll_type = unroll_type ty keys in
  let unroll_exp e = unroll_exp ty keys e in
  let has_target_type e = has_target_type ty e in
  let get_index k = get_index keys k in
  let ty_unrolled = unroll_type ty in
  let unrolled_exp =
    match e.e with
    | EVal v ->
      (* No way to construct map value directly *)
      e_val (avalue (v, mapo unroll_type v.vty, v.vspan))
    | EVar _ -> e
    | EFun f ->
      efun
        { f with
          argty= mapo unroll_type f.argty; resty= mapo unroll_type f.resty; body= unroll_exp f.body }
    | EApp (e1, e2) ->
      eapp (unroll_exp e1) (unroll_exp e2)
    | EIf (e1, e2, e3) ->
      eif (unroll_exp e1) (unroll_exp e2) (unroll_exp e3)
    | ELet (x, e1, e2) ->
      elet x (unroll_exp e1) (unroll_exp e2)
    | ETuple es ->
      etuple (BatList.map unroll_exp es)
    | ERecord map ->
      erecord (StringMap.map unroll_exp map)
    | EProject (e1, l) -> eproject (unroll_exp e1) l
    | ESome e1 ->
      esome (unroll_exp e1)
    | EMatch (e1, bs) ->
      ematch
        (unroll_exp e1)
        (mapBranches (fun (p,e) -> (p, unroll_exp e)) bs)
    | ETy (e1, _) -> unroll_exp e1
    | EOp (op, es) ->
      match op, es with
      | And, _
      | Or, _
      | Not, _
      | UAdd _, _
      | USub _, _
      | ULess _, _
      | ULeq _, _
      | NLess, _
      | NLeq, _
      | Eq, _ ->
        eop op (BatList.map unroll_exp es)
      | MCreate, [e1] ->
        if not (has_target_type e) then
          eop MCreate [unroll_exp e1]
        else
          etuple (BatList.make (BatList.length keys) (unroll_exp e1))
      | MGet, [map; k] ->
        if not (has_target_type map) then
          eop MGet [unroll_exp map; unroll_exp k]
        else
          begin
            (* Distinguish between constant and variable keys *)
            if is_value k then
              begin
                let val_ty =
                  match ty with
                  | TMap (_, ty) -> ty
                  | _ -> failwith "impossible"
                in
                let index =
                  match get_index k with
                  | Some n -> n
                  | None ->
                    failwith "Encountered unrecognized key during map unrolling"
                in
                let x = Var.fresh "UnrollingGetVar" in
                let plist =
                  BatList.mapi (fun i _ -> if i = index then PVar x else PWild) keys
                in
                let pattern = PTuple plist in
                ematch (unroll_exp map) (addBranch pattern (aexp (evar x, Some (val_ty), e.espan)) emptyBranch)
              end
            else
              begin
                let pvars = BatList.mapi (fun i _ ->
                    PVar (Var.fresh (Printf.sprintf "MapGet-%d" i)))
                    keys
                in
                let tyv = match e.ety with
                  | Some (TMap (_, tyv)) -> Some tyv
                  | _ -> None
                in
                (* need expression to pattern function
                   s.t. k1 -> p1, etc.
                *)
                let branches = BatList.map2i (fun i pvi ki ->
                    match pvi with
                    | PVar x ->
                      (exp_to_pattern ki,
                       aexp (evar x, tyv, e.espan))
                    | _ -> failwith "impossible") pvars keys
                in
                let inner_match =
                  aexp(ematch k (BatList.fold_left (fun acc (p,x) ->
                      addBranch p x acc) emptyBranch branches),
                       tyv, e.espan)
                in
                let m = unroll_exp map in
                aexp(ematch m (addBranch (PTuple pvars) inner_match emptyBranch),
                     tyv, e.espan)
              end
          end
      | MSet, [map; k; setval] ->
        if not (has_target_type map) then
          eop MSet [unroll_exp map; unroll_exp k; unroll_exp setval]
        else
          begin
            match get_index k with
            | None -> unroll_exp map
            | Some index ->
              let freshvars =
                BatList.map (fun _ -> Var.fresh "UnrollingSetVar") keys
              in
              let pattern =
                PTuple (BatList.map (fun var -> PVar var) freshvars)
              in
              let val_ty =
                match ty (* Type of the map we're unrolling *) with
                | TMap (_, ty) -> ty
                | _ -> failwith "impossible"
              in
              let result =
                BatList.mapi
                  (fun i var ->
                     if i <> index then (aexp (evar var, Some (val_ty), e.espan))
                     else unroll_exp setval)
                  freshvars
              in
              ematch (unroll_exp map) (addBranch pattern (aexp ((etuple result), Some (ty_unrolled), e.espan)) emptyBranch)
          end
      | MMap, [f; map] ->
        if not (has_target_type map) then
          eop MMap [unroll_exp f; unroll_exp map]
        else
          let val_ty =
            match ty (* Type of the map we're unrolling *) with
            | TMap (_, ty) -> ty
            | _ -> failwith "impossible"
          in          let f' = unroll_exp f in
          let freshvars =
            BatList.map (fun _ -> Var.fresh "UnrollingMapVar") keys
          in
          let pattern =
            PTuple (BatList.map (fun var -> PVar var) freshvars)
          in
          let freshvars =
            BatList.map (fun var -> aexp (evar var, Some (val_ty), e.espan)) freshvars
          in
          let result =
            BatList.map
              (fun var -> aexp (eapp f' var, Some (val_ty), e.espan))
              freshvars
          in
          ematch (unroll_exp map) (addBranch pattern (aexp ((etuple result), Some (ty_unrolled), e.espan)) emptyBranch)
      | MMapFilter, [p; f; map] ->
        if not (has_target_type map) then
          eop MMapFilter [unroll_exp p; unroll_exp f; unroll_exp map]
        else
          let f' = unroll_exp f in
          let p' = unroll_exp p in
          let freshvars =
            BatList.map (fun _ -> Var.fresh "UnrollingMapFilterVar") keys
          in
          let pattern =
            PTuple (BatList.map (fun var -> PVar var) freshvars)
          in
          let val_ty =
            match ty (* Type of the map we're unrolling *) with
            | TMap (_, ty) -> ty
            | _ -> failwith "impossible"
          in
          let make_result k var =
            let if_exp =
              eif
                (aexp (eapp p' k, Some (TBool), e.espan))
                (aexp (eapp f' var, Some (val_ty), e.espan))
                var
            in
            aexp (if_exp, Some (val_ty), e.espan)
          in
          let freshvars =
            BatList.map (fun var -> aexp (evar var, Some (val_ty), e.espan)) freshvars
          in
          let result =
            BatList.map2 make_result keys freshvars
          in
          ematch (unroll_exp map) (addBranch pattern (aexp ((etuple result), Some (ty_unrolled), e.espan)) emptyBranch)
      | MMerge, f :: map1 :: map2 :: _ ->
        (* Should be redundant, since I think typing assumes the arguments to
           MMerge have the same type *)
        if not ((has_target_type map1) && (has_target_type map2)) then
          eop MMerge [unroll_exp f; unroll_exp map1; unroll_exp map2]
        else
          let f' = unroll_exp f in
          let val_ty =
            match ty (* Map type we're unrolling *) with
            | TMap (_, ty) -> ty
            | _ -> failwith "impossible"
          in
          let freshvars1, freshvars2 =
            BatList.map (fun _ -> Var.fresh "UnrollingMMergeVar1") keys,
            BatList.map (fun _ -> Var.fresh "UnrollingMMergeVar2") keys
          in
          let pattern =
            PTuple([
                PTuple (BatList.map (fun var -> PVar var) freshvars1);
                PTuple (BatList.map (fun var -> PVar var) freshvars2)
              ])
          in
          let result =
            BatList.map2
              (fun var1 var2 ->
                 let v1 = aexp (evar var1, Some (val_ty), e.espan) in
                 let v2 = aexp (evar var2, Some (val_ty), e.espan) in
                 let fst_app =
                   aexp ((eapp f' v1), Some (TArrow (val_ty, val_ty)), e.espan)
                 in
                 aexp (eapp fst_app v2, Some (val_ty), e.espan))
              freshvars1 freshvars2
          in
          let map_pair =
            aexp
              ((etuple [unroll_exp map1; unroll_exp map2]),
               Some (TTuple [unroll_type ty; unroll_type ty]),
               e.espan)
          in
          ematch
            map_pair
            (addBranch pattern (aexp ((etuple result), Some (ty_unrolled), e.espan)) emptyBranch)
      | _ ->
        failwith @@ "Failed to unroll map: Incorrect number of arguments to map operation : "
                    ^ Printing.exp_to_string e
  in
  aexp (unrolled_exp, mapo unroll_type e.ety, e.espan)
;;

let unroll_decl
    (ty : ty)
    (keys : exp list)
    (decl : declaration)
  : declaration
  =
  let unroll_exp = unroll_exp ty keys in
  let unroll_type = unroll_type ty keys in
  match decl with
  | DLet (var, tyo, e) -> DLet (var, mapo unroll_type tyo, unroll_exp e)
  | DSymbolic (var, toe) ->
    let toe' =
      match toe with
      | Ty t -> Ty(unroll_type t)
      | Exp e -> Exp(unroll_exp e)
    in
    DSymbolic (var, toe')
  | DATy t -> DATy (unroll_type t)
  | DUserTy (l,t) -> DUserTy (l, unroll_type t)
  | DMerge e -> DMerge (unroll_exp e)
  | DTrans e -> DTrans (unroll_exp e)
  | DInit e -> DInit (unroll_exp e)
  | DAssert e -> DAssert (unroll_exp e)
  | DPartition e -> DPartition (unroll_exp e) (* partitioning *)
  | DInterface e -> DInterface (unroll_exp e) (* partitioning *)
  | DRequire e -> DRequire (unroll_exp e)
  | DNodes _
  | DEdges _ -> decl
;;

let unroll_one_map_type
    (ty : ty)
    (keys : exp list)
    (decls : declarations)
  : declarations
  =
  (* According to the docs, ExpSet.elements returns a sorted list.
     This is important because we need a consistent numbering for
     our keys *)
  BatList.map (unroll_decl ty keys) decls
;;
