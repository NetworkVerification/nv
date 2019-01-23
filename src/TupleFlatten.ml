open Collections
open Syntax

let rec flatten_ty ty =
  match ty with
  | TVar {contents= Link t} -> flatten_ty t
  | TBool -> ty
  | TInt _ -> ty
  | TArrow (t1, t2) ->
     let ty1 = flatten_ty t1 in
     (match ty1 with
     | TTuple ts ->
        BatList.fold_right (fun t acc ->
            TArrow (t, acc)) ts (flatten_ty t2)
     | _ ->
        TArrow (ty1, flatten_ty t2))
  | TTuple ts ->
     let ts = BatList.map flatten_ty ts in
     let ts' = BatList.fold_right (fun ty acc ->
                   match ty with
                   | TTuple ts -> BatList.append ts acc
                   | _ -> ty :: acc) ts []
     in
     TTuple ts'
  | TOption ty -> TOption (flatten_ty ty)
  | TMap (ty1, ty2) ->
     TMap (flatten_ty ty1, flatten_ty ty2)
  | QVar _ | TVar _ -> failwith "internal error (flatten_ty)"

let rec flatten_val v =
  match v.v with
  | VBool _ | VInt _ | VMap _ | VOption None -> v
  | VOption (Some v) ->
     avalue (voption (Some (flatten_val v)), Some (flatten_ty (oget v.vty)), v.vspan)
  | VTuple vs ->
     let vs = BatList.map flatten_val vs in
     let vs' = BatList.fold_right (fun v acc ->
                   match v.v with
                   | VTuple vs -> BatList.append vs acc
                   | _ -> v :: acc) vs []
     in
     avalue (vtuple vs', Some (flatten_ty (oget v.vty)), v.vspan)
  | VClosure _ -> failwith "Closures not yet implemented"
                
let rec flatten_exp e : exp =
  match e.e with
  | ETy (e, ty) -> flatten_exp e
  | EVal v ->
     let v = flatten_val v in
     (* Printf.printf "%s\n" (Syntax.show_value ~show_meta:false v); *)
     aexp (e_val v, v.vty, v.vspan)
  | EVar x ->
     let ty = flatten_ty (oget e.ety) in
     (match ty with
      | TTuple ts ->
         let es = 
           BatList.mapi (fun i ty ->
               aexp(evar (proj_var i x), Some ty, Span.default)) ts
         in
         aexp(etuple es, Some ty, e.espan)
      | _ ->
         aexp(e, Some ty, e.espan))
  | EFun {arg = x; argty = Some xty; resty= Some resty; body= body} ->
     let body = flatten_exp body in
     let xty = flatten_ty xty in
     (match xty with
      | TTuple ts ->
         BatList.fold_righti (fun i ty acce ->
             aexp (efun
                     { arg = proj_var i x;
                       argty = Some ty;
                       resty = acce.ety;
                       body = acce}, Some (TArrow (ty,oget acce.ety)), e.espan))
                             ts body
      | _ ->
         aexp (efun
                 { arg = x;
                   argty = Some xty;
                   resty = body.ety;
                   body = body}, Some (TArrow (xty,oget body.ety)), e.espan))
  | EFun {arg = x; argty = _; resty= _; body= body} ->
     failwith "missing types in function declaration"
  | EApp (e1, e2) ->
     let e2 = flatten_exp e2 in
     (match e2.e with
      | ETuple es ->
         aexp (apps (flatten_exp e1) es, Some (flatten_ty (oget e.ety)), e.espan)
      | _ ->
         aexp (eapp (flatten_exp e1) e2, Some (flatten_ty (oget e.ety)), e.espan))
  | EIf (e1, e2, e3) ->
     aexp (eif (flatten_exp e1) (flatten_exp e2) (flatten_exp e3),
           Some (flatten_ty (oget e.ety)), e.espan)
  | ELet (x, e1, e2) ->
     let e1 = flatten_exp e1 in
     let ty = flatten_ty (oget e.ety) in
     (match e1.e with
      | ETuple es ->
         let es = BatList.mapi (fun i e -> (proj_var i x, e)) es in
         BatList.fold_right (fun (xi, ei) acc ->
             aexp (elet xi ei acc, Some ty, ei.espan)) es (flatten_exp e2)
      | _ ->
         (match (oget e1.ety) with
          | TTuple ts ->
             let ps = BatList.mapi (fun i _ -> PVar (proj_var i x)) ts in
             aexp (ematch e1 [(PTuple ps, flatten_exp e2)],
                   Some ty, e.espan)
          | _ ->
             aexp (elet x e1 (flatten_exp e2), Some ty, e.espan)))
  | ETuple es ->
     let es = List.map flatten_exp es in
     let es' = List.fold_right (fun e acc ->
                   match e.e with
                   | ETuple es -> es @ acc
                   | EVal v ->
                      (match v.v with
                       | VTuple vs -> (BatList.map e_val vs) @ acc
                       | _ -> e :: acc)
                   | _ -> e :: acc) es []
     in
     aexp (etuple es', Some (flatten_ty (oget e.ety)), e.espan)
  | ESome e1 ->
     aexp (esome (flatten_exp e1), Some (flatten_ty (oget e.ety)), Span.default)
  | EMatch (e1, bs) ->
     aexp (ematch (flatten_exp e1) (flatten_branches bs ((oget e1.ety))),
           Some (flatten_ty (oget e.ety)),
           e.espan)
  | EOp (op, es) -> (
    match op with
    | And
    | Or
    | Not
    | UAdd _
    | USub _
    | UEq
    | ULess _
    | AtMost _
    | MCreate
    | MGet
    | MSet
    | ULeq _ ->
       aexp (eop op (BatList.map flatten_exp es),
             Some (flatten_ty (oget e.ety)), e.espan)
    | _ -> failwith "TODO: implement tupple flattening for more map operations")
        
and flatten_branches bs ty =
  let rec flatten_pattern p ty =
    let ty = get_inner_type ty in
    match p with
    | POption (Some p) ->
       (match ty with
       | TOption t ->
          POption (Some (flatten_pattern p t))
       | _ -> failwith "expected option type")
    | PTuple ps ->
       (match ty with
        | TTuple ts ->
           let ps = BatList.map2 flatten_pattern ps ts in
           let ps' = BatList.fold_right (fun p acc ->
                         match p with
                         | PTuple ps -> ps @ acc
                         | _ -> p :: acc) ps []
           in
           PTuple ps'
        | _ -> failwith "expected tuple type")
    | PVar x ->
       (match ty with
        | TTuple ts ->
           (match flatten_ty (TTuple ts) with
            | TTuple ts ->
              let ps = BatList.mapi (fun i _ -> PVar (proj_var i x)) ts in
              PTuple ps
            | _ -> failwith "must be ttuple")
        | _ -> p)
    | PWild ->
       (match ty with
        | TTuple ts ->
           (match flatten_ty (TTuple ts) with
            | TTuple ts ->
               let ps = BatList.map (fun _ -> PWild) ts in
               PTuple ps
            | _ -> failwith "must be ttuple")
        | _ -> p)
    | PBool _ | PInt _ | POption None  -> p
  in
  BatList.map (fun (p, e) -> (flatten_pattern p ty, flatten_exp e)) bs
             
let flatten_decl_single d =
  match d with
  | DLet (x, oty, e) -> DLet (x, Some (flatten_ty (oget oty)), flatten_exp e)
  | DMerge e -> DMerge (flatten_exp e)
  | DTrans e -> DTrans (flatten_exp e)
  | DInit e -> DInit (flatten_exp e)
  | DAssert e -> DAssert (flatten_exp e)
  | DRequire e -> DRequire (flatten_exp e)
  | DATy aty -> DATy (flatten_ty aty)
  | DNodes _ | DEdges _ -> d
  | DSymbolic _ -> failwith "impossible"

(* assumes symbolic expressions are values (no if-then-else etc.)
   maybe they should just be values?*)
let flatten_decl d =
  match d with
  | DSymbolic (x, Exp e) ->
     let e = flatten_exp e in
     (match e.e with
      | ETuple es ->
         BatList.mapi (fun i ei ->
             DSymbolic (proj_var i x, Exp ei)) es
      | _ -> [DSymbolic (x, Exp e)])
  | DSymbolic (x, Ty ty) ->
     (match flatten_ty ty with
     | TTuple ts ->
        BatList.mapi (fun i ty -> DSymbolic (proj_var i x, Ty ty)) ts
     | ty -> [DSymbolic (x, Ty ty)])
  | _ -> [flatten_decl_single d]

let flatten ds =
  BatList.map flatten_decl ds |> BatList.concat
