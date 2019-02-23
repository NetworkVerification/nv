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

let rec unroll_type
    (ty : ty)
    (keys : exp list)
    (ty2 : ty)
  : ty
  =
  (* print_endline @@  "Unrolling type: " ^ Printing.ty_to_string ty2; *)
  let unroll_type = unroll_type ty keys in
  match (canonicalize_type ty2) with
  | TBool
  | TInt _ ->
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
  let unroll_exp e = unroll_exp ty keys e in
  let has_target_type e = has_target_type ty e in
  let get_index k = get_index keys k in
  let unrolled_exp =
    match e.e with
    | EVal _ (* No way to construct map value directly *)
    | EVar _ ->
      exp e.e
    | EFun f ->
      efun
        { f with
          argty= None; resty= None; body= unroll_exp f.body }
    | EApp (e1, e2) ->
      eapp (unroll_exp e1) (unroll_exp e2)
    | EIf (e1, e2, e3) ->
      eif (unroll_exp e1) (unroll_exp e2) (unroll_exp e3)
    | ELet (x, e1, e2) ->
      elet x (unroll_exp e1) (unroll_exp e2)
    | ETuple es ->
      etuple (BatList.map unroll_exp es)
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
      | UEq, _ ->
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
          let pattern =
            PTuple(plist)
          in
          ematch (unroll_exp map) (addBranch pattern (evar x) emptyBranch)
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
              let result =
                BatList.mapi
                  (fun i var ->
                     if i <> index then evar var
                     else unroll_exp setval)
                  freshvars
              in
              ematch (unroll_exp map) (addBranch pattern (etuple result) emptyBranch)
          end
      | MMap, [f; map] ->
        if not (has_target_type map) then
          eop MMap [unroll_exp f; unroll_exp map]
        else
          let f' = unroll_exp f in
          let freshvars =
            BatList.map (fun _ -> Var.fresh "UnrollingMapVar") keys
          in
          let pattern =
            PTuple (BatList.map (fun var -> PVar var) freshvars)
          in
          let result =
            BatList.map
              (fun var -> eapp f' (evar var))
              freshvars
          in
          ematch (unroll_exp map) (addBranch pattern (etuple result) emptyBranch)
      | MMapFilter, [p; f; map] ->
        if not (has_target_type map) then
          eop MMapFilter [unroll_exp p; unroll_exp f; unroll_exp map]
        else
          let f' = unroll_exp f in
          let p' = unroll_exp p in
          let freshvars =
            List.map (fun _ -> Var.fresh "UnrollingMapFilterVar") keys
          in
          let pattern =
            PTuple (BatList.map (fun var -> PVar var) freshvars)
          in
          let make_result k var =
            eif (eapp p' k) (eapp f' (evar var)) (evar var)
          in
          let result =
            BatList.map2 make_result keys freshvars
          in
          ematch (unroll_exp map) (addBranch pattern (etuple result) emptyBranch)
      | MMerge, f :: map1 :: map2 :: _ ->
        if not ((has_target_type map1) && (has_target_type map2)) then
          eop MMerge [unroll_exp f; unroll_exp map1; unroll_exp map2]
        else
          let f' = unroll_exp f in
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
              (fun var1 var2 -> eapp (eapp f' (evar var1)) (evar var2))
              freshvars1 freshvars2
          in
          ematch
            (etuple [unroll_exp map1; unroll_exp map2])
            (addBranch pattern (etuple result) emptyBranch)
      | _ ->
        failwith @@ "Failed to unroll map: Incorrect number of arguments to map operation : "
                    ^ Printing.exp_to_string e
  in
  aexp (unrolled_exp, None, e.espan)
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
  | DLet (var, tyo, e) ->
     (* Printf.printf "crashes on:%s\n" (Printing.exp_to_string e); *)
    let tyo' =
      match tyo with
      | Some t -> Some(unroll_type t)
      | None -> None
    in
    DLet (var, tyo', unroll_exp e)
  | DSymbolic (var, toe) ->
    let toe' =
      match toe with
      | Ty t -> Ty(unroll_type t)
      | Exp e -> Exp(unroll_exp e)
    in
    DSymbolic (var, toe')
  | DATy t -> DATy (unroll_type t)
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
    (keys : exp list)
    (decls : declarations)
  : declarations
  =
  (* According to the docs, ExpSet.elements returns a sorted list.
     This is important because we need a consistent numbering for
     our keys *)
  BatList.map (unroll_decl ty keys) decls
;;
