open Syntax
open Collections

let has_target_type (target : ty) (e : exp) : bool =
  match e.ety with
  | Some (ty) -> equal_tys target ty
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

let rec unroll_in_exp
    (ty : ty)
    (keys : exp list)
    (e : exp)
  : exp
  =
  let unroll_in_exp e = unroll_in_exp ty keys e in
  let has_target_type e = has_target_type ty e in
  let get_index k = get_index keys k in
  match e.e with
  | EVar _ (* No way to construct map value directly *)
  | EVal _ ->
    exp e.e
  | EFun f ->
    efun
      { f with
        argty= None; resty= None; body= unroll_in_exp f.body }
  | EApp (e1, e2) ->
    eapp (unroll_in_exp e1) (unroll_in_exp e2)
  | EIf (e1, e2, e3) ->
    eif (unroll_in_exp e1) (unroll_in_exp e2) (unroll_in_exp e3)
  | ELet (x, e1, e2) ->
    elet x (unroll_in_exp e1) (unroll_in_exp e2)
  | ETuple es ->
    etuple (List.map unroll_in_exp es)
  | ESome e1 ->
    esome (unroll_in_exp e1)
  | EMatch (e1, bs) ->
    ematch
      (unroll_in_exp e1)
      (List.map (fun (p, e) -> (p, unroll_in_exp e)) bs)
  | ETy (e1, _) -> unroll_in_exp e1
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
      eop op (List.map unroll_in_exp es)
    | MCreate, [e] ->
      etuple (BatList.make (List.length keys) (unroll_in_exp e))
    | MGet, [map; k] ->
      if not (has_target_type map) then
        eop MGet [unroll_in_exp map; unroll_in_exp k]
      else
        let index =
          match get_index k with
          | Some n -> n
          | None ->
            failwith "Encountered unrecognized key during map unrolling"
        in
        let x = Var.fresh "UnrollingGetVar" in
        let pattern =
          PTuple(
            BatList.make index PWild @
            PVar x ::
            BatList.make (List.length keys - index - 1) PWild
          )
        in
        ematch (unroll_in_exp map) [(pattern, evar x)]
    | MSet, [map; k; setval] ->
      if not (has_target_type map) then
        eop MSet [unroll_in_exp map; unroll_in_exp k; unroll_in_exp setval]
      else
        begin
          match get_index k with
          | None -> unroll_in_exp map
          | Some index ->
            let freshvars =
              List.map (fun _ -> Var.fresh "UnrollingSetVar") keys
            in
            let pattern =
              PTuple (List.map (fun var -> PVar var) freshvars)
            in
            let result =
              List.mapi
                (fun i var ->
                   if i <> index then evar var
                   else unroll_in_exp setval)
                freshvars
            in
            ematch (unroll_in_exp map) [(pattern, etuple result)]
        end
    | MMap, [f; map] ->
      if not (has_target_type map) then
        eop MMap [unroll_in_exp f; unroll_in_exp map]
      else
        let f' = unroll_in_exp f in
        let freshvars =
          List.map (fun _ -> Var.fresh "UnrollingMapVar") keys
        in
        let pattern =
          PTuple (List.map (fun var -> PVar var) freshvars)
        in
        let result =
          List.map
            (fun var -> eapp f' (evar var))
            freshvars
        in
        ematch (unroll_in_exp map) [(pattern, etuple result)]
    | MMapFilter, [p; f; map] ->
      if not (has_target_type map) then
        eop MMapFilter [unroll_in_exp p; unroll_in_exp f; unroll_in_exp map]
      else
        let f' = unroll_in_exp f in
        let p' = unroll_in_exp p in
        let freshvars =
          List.map (fun _ -> Var.fresh "UnrollingMapFilterVar") keys
        in
        let pattern =
          PTuple (List.map (fun var -> PVar var) freshvars)
        in
        let make_result k var =
          eif (eapp p' k) (eapp f' (evar var)) (evar var)
        in
        let result =
          List.map2 make_result keys freshvars
        in
        ematch (unroll_in_exp map) [(pattern, etuple result)]
    | MMerge, [f; map1; map2] ->
      if not ((has_target_type map1) && (has_target_type map2)) then
        eop MMerge [unroll_in_exp f; unroll_in_exp map1; unroll_in_exp map2]
      else
        let f' = unroll_in_exp f in
        let freshvars1, freshvars2 =
          List.map (fun _ -> Var.fresh "UnrollingMMergeVar1") keys,
          List.map (fun _ -> Var.fresh "UnrollingMMergeVar2") keys
        in
        let pattern =
          PTuple([
            PTuple (List.map (fun var -> PVar var) freshvars1);
            PTuple (List.map (fun var -> PVar var) freshvars2)
          ])
        in
        let result =
          List.map2
            (fun var1 var2 -> eapp (eapp f' (evar var1)) (evar var2))
            freshvars1 freshvars2
        in
        ematch
          (etuple [unroll_in_exp map1; unroll_in_exp map2])
          [(pattern, etuple result)]
    | _ ->
      failwith "Failed to unroll map: Incorrect number of arguments to map operation"
;;

let unroll_in_decl
    (ty : ty)
    (keys : exp list)
    (decl : declaration)
  : declaration
  =
  failwith "AAS"
;;

let unroll_one_type
    (ty : ty)
    (keys : ExpSet.t)
    (decls : declarations)
  : declarations
  =
  (* According to the docs, ExpSet.elements returns a sorted list.
     This is important because we need a consistent numbering for
     our keys *)
  List.map (unroll_in_decl ty (ExpSet.elements keys)) decls
;;
