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

let get_index_const keys k =
  let const_keys, _ = keys in
  try
    let index, _ =
      BatList.findi (fun _ e -> compare_es e k = 0) const_keys
    in
    Some(index)
  with
  | _ -> None
;;

let get_index_symb keys symb =
  let const_keys, symb_keys = keys in
  try
    let index, _ =
      BatList.findi (fun _ s -> Var.equal s symb) symb_keys
    in
    Some(index + List.length const_keys)
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
    (keys : exp list * var list)
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
      let const_keys, symb_keys = keys in
      (* Don't need to recurse since types cannot contain themselves *)
      TTuple (BatList.make (BatList.length const_keys + BatList.length symb_keys) (canonicalize_type val_ty))
    else
      TMap (unroll_type key_ty, unroll_type val_ty)
  | TRecord map -> TRecord (StringMap.map unroll_type map)
  | QVar tyname -> QVar tyname
  (* failwith "Cannot unroll a type containing a QVar!"; *)
  | TVar _ ->
    failwith "Encountered TVar after canonicalization"
;;

let rec unroll_get_or_set
    (keys : exp list * var list)
    (mk_op : int -> exp)
    (ety : ty option)
    (espan : Span.t)
    (k : exp) =
  let get_index_const = get_index_const keys in
  let get_index_symb = get_index_symb keys in
  match get_index_const k with
  | Some n ->
    (* Constant key - no need to write a match *)
    mk_op n
  | None ->
    let const_keys, symb_keys = keys in
    let const_branches =
      const_keys
      |> List.mapi
        (fun i k ->
           (exp_to_pattern k, mk_op i))
      |> List.fold_left
        (fun acc (p,x) -> addBranch p x acc) emptyBranch
    in
    match k.ety with
    | Some (TNode)
    | Some (TEdge) ->
      (* We know all possible node and edge values in advance, so just
         match the variable with each of them *)
      ematch k const_branches
    | _ ->
      (* Otherwise, we require that the key be be a symbolic variable *)
      let _, index =
        match k.e with
        | EVar v ->
          begin
            match get_index_symb v with
            | Some i -> v,i
            | None -> failwith @@
              "Encountered non-constant, non-symbolic variable key whose type is not TNode or TEdge: " ^
              Printing.exp_to_string k
          end
        | _ -> failwith @@
          "Encountered non-constant, non-variable key whose type is not TNode or TEdge: " ^
          Printing.exp_to_string k
      in
      (* List of symbolics with a strictly lower index *)
      let preceding_symb_keys =
        BatList.take index symb_keys
      in
      let big_if =
        List.fold_left
          (fun acc v ->
             let cmp =
               (* Compare our key to the symbolic variable v *)
               aexp (eop Eq [k; aexp (evar v, k.ety, k.espan)], Some TBool, espan)
             in
             let ethen =
               (* If they're the same value, use v's index instead of k's *)
               v |> get_index_symb |> oget |> mk_op
             in
             aexp (eif cmp ethen acc, ety, espan)
          )
          (* If we have a different value from all the lower-index symbolics,
             use our own index *)
          (mk_op index)
          preceding_symb_keys
      in
      let final_branches = addBranch PWild big_if const_branches in
      ematch k final_branches
;;

let rec unroll_exp
    (ty : ty)
    (keys : exp list * var list)
    (e : exp)
  : exp
  =
  let unroll_type = unroll_type ty keys in
  let unroll_exp e = unroll_exp ty keys e in
  let has_target_type e = has_target_type ty e in

  let ty_unrolled = unroll_type ty in
  let const_keys, symb_keys = keys in
  let unrolled_size = List.length const_keys + List.length symb_keys in
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
      | Eq, _
      | TGet _, _
      | TSet _, _->
        eop op (BatList.map unroll_exp es)
      | MCreate, [e1] ->
        if not (has_target_type e) then
          eop MCreate [unroll_exp e1]
        else
          etuple (BatList.make unrolled_size (unroll_exp e1))
      | MGet, [map; k] ->
        if not (has_target_type map) then
          eop MGet [unroll_exp map; unroll_exp k]
        else
          let unrolled_map = unroll_exp map in
          let unrolled_ety = mapo unroll_type e.ety in
          let mk_op =
            (fun index ->
               aexp (eop (TGet (unrolled_size, index, index)) [unrolled_map],
                     unrolled_ety, e.espan))
          in
          unroll_get_or_set keys mk_op unrolled_ety e.espan k
      | MSet, [map; k; setval] ->
        if not (has_target_type map) then
          eop MSet [unroll_exp map; unroll_exp k; unroll_exp setval]
        else
          let unrolled_map = unroll_exp map in
          let unrolled_setval = unroll_exp setval in
          let unrolled_ety = mapo unroll_type e.ety in
          let mk_op =
            (fun index ->
               aexp (eop (TSet (unrolled_size, index, index)) [unrolled_map; unrolled_setval],
                     unrolled_ety, e.espan))
          in
          unroll_get_or_set keys mk_op unrolled_ety e.espan k
      | MMap, [f; map] ->
        if not (has_target_type map) then
          eop MMap [unroll_exp f; unroll_exp map]
        else
          let val_ty =
            match ty (* Type of the map we're unrolling *) with
            | TMap (_, ty) -> ty
            | _ -> failwith "impossible"
          in
          let f' = unroll_exp f in
          let freshvars =
            BatList.map (fun _ -> Var.fresh "UnrollingMapVar") symb_keys @
            BatList.map (fun _ -> Var.fresh "UnrollingMapVar") const_keys
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
          let key_ty =
            match ty (* Type of the map we're unrolling *) with
            | TMap (ty, _) -> ty
            | _ -> failwith "impossible"
          in
          let f' = unroll_exp f in
          let p' = unroll_exp p in
          let all_keys =
            List.map (fun v -> aexp (evar v, Some key_ty, e.espan)) symb_keys @
            const_keys
          in
          let freshvars =
            BatList.map (fun _ -> Var.fresh "UnrollingMapFilterVar") all_keys
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
            BatList.map2 make_result all_keys freshvars
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
            let lst =
              BatList.make (List.length symb_keys + List.length const_keys) ()
            in
            BatList.map (fun _ -> Var.fresh "UnrollingMergeVar1") lst,
            BatList.map (fun _ -> Var.fresh "UnrollingMergeVar2") lst
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
      | MFoldNode, [f; map; acc]
      | MFoldEdge, [f; map; acc] ->
        if not (has_target_type map) then
          eop op [unroll_exp f; unroll_exp acc; unroll_exp map]
        else
          (* fold f acc m ->
             (f (f acc k1 v1) k2 v2)
          *)
          let key_ty, val_ty =
            match ty (* Type of the map we're unrolling *) with
            | TMap (kty, vty) -> kty, vty
            | _ -> failwith "impossible"
          in
          let acc' = unroll_exp acc in
          let acc_ty = oget acc'.ety in
          let f' = unroll_exp f in
          let symb_var_keys =
            List.map (fun v -> aexp (evar v, Some key_ty, e.espan)) symb_keys
          in
          let freshvars =
            BatList.map (fun k -> (k, Var.fresh "UnrollingFoldVar")) (symb_var_keys @ const_keys)
          in
          let pattern =
            PTuple (BatList.map (fun (_, var) -> PVar var) freshvars)
          in
          let fold_vars =
            BatList.map (fun (k, v) -> k, aexp (evar v, Some (val_ty), e.espan)) freshvars
          in
          let result =
            BatList.fold_left
              (fun acc (k, v) ->
                 let app1 = aexp (eapp f' k, Some (TArrow (val_ty, TArrow(acc_ty, acc_ty))), e.espan) in
                 let app2 = aexp (eapp app1 v, Some (TArrow(acc_ty, acc_ty)), e.espan) in
                 let app3 = aexp (eapp app2 acc, Some (acc_ty), e.espan) in
                 app3)
              acc'
              fold_vars
          in
          ematch (unroll_exp map) (addBranch pattern result emptyBranch)
      | _ ->
        failwith @@ "Failed to unroll map: Incorrect number of arguments to map operation : "
                    ^ Printing.exp_to_string e
  in
  aexp (unrolled_exp, mapo unroll_type e.ety, e.espan)
;;

let unroll_decl
    (ty : ty)
    (keys : exp list * var list)
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
  | DRequire e -> DRequire (unroll_exp e)
  | DNodes _
  | DEdges _ -> decl
;;

let unroll_one_map_type
    (ty : ty)
    (keys : exp list * var list)
    (decls : declarations)
  : declarations
  =
  (* According to the docs, ExpSet.elements returns a sorted list.
     This is important because we need a consistent numbering for
     our keys *)
  BatList.map (unroll_decl ty keys) decls
;;
