open Collections
open Syntax

let rec flatten_ty ty =
  match ty with
  | TVar {contents= Link t} -> flatten_ty t
  | TBool -> ty
  | TInt _ -> ty
  | TArrow (t1, t2) ->
     TArrow (flatten_ty t1, flatten_ty t2)
  | TTuple ts ->
     let ts = List.map flatten_ty ts in
     let ts' = List.fold_right (fun ty acc ->
                   match ty with
                   | TTuple ts -> ts @ acc
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
     let vs = List.map flatten_val vs in
     let vs' = List.fold_right (fun v acc ->
                   match v.v with
                   | VTuple vs -> vs @ acc
                   | _ -> v :: acc) vs []
     in
     avalue (vtuple vs', Some (flatten_ty (oget v.vty)), v.vspan)
  | VClosure _ -> failwith "Closures not yet implemented"
  
let rec flatten_exp e : exp =
  match e.e with
  | ETy (e, ty) -> flatten_exp e
  | EVal v ->
     let v = flatten_val v in
     aexp (e_val v, v.vty, v.vspan)
  | EVar _ -> aexp(e, Some (flatten_ty (oget e.ety)), e.espan)
  | EFun f ->
      aexp (efun
              { f with
                argty= Some (flatten_ty (oget f.argty));
                resty= Some (flatten_ty (oget f.resty));
                body= flatten_exp f.body },
            Some (flatten_ty (TArrow (oget f.argty, oget f.resty))), e.espan)
  | EApp (e1, e2) ->
     aexp (eapp (flatten_exp e1) (flatten_exp e2), Some (flatten_ty (oget e.ety)), e.espan)
  | EIf (e1, e2, e3) ->
     aexp (eif (flatten_exp e1) (flatten_exp e2) (flatten_exp e3),
           Some (flatten_ty (oget e.ety)), e.espan)
  | ELet (x, e1, e2) ->
     aexp(elet x (flatten_exp e1) (flatten_exp e2),
          Some (flatten_ty (oget e.ety)), e.espan)
  | ETuple es ->
     let es = List.map flatten_exp es in
     let es' = List.fold_right (fun e acc ->
                   match e.e with
                   | ETuple es -> es @ acc
                   | _ -> e :: acc) es []
     in
     aexp (etuple (List.map flatten_exp es'), Some (flatten_ty (oget e.ety)), e.espan)
  | ESome e1 ->
     aexp (esome (flatten_exp e1), Some (flatten_ty (oget e.ety)), Span.default)
  | EMatch (e1, bs) ->
     aexp (ematch (flatten_exp e1) (flatten_branches bs),
           Some (flatten_ty (oget e1.ety)),
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
    | ULeq _ ->
       aexp (eop op (List.map flatten_exp es),
             Some (flatten_ty (oget e.ety)), e.espan)
    | _ -> failwith "TODO: implement option flattening for maps")
        
and flatten_branches bs =
  let rec flatten_pattern p =
    match p with
    | POption (Some p) -> POption (Some (flatten_pattern p))
    | PTuple ps ->
       let ps = List.map flatten_pattern ps in
       let ps' = List.fold_right (fun p acc ->
                     match p with
                     | PTuple ps -> ps @ acc
                     | _ -> p :: acc) ps []
       in
       PTuple (List.map flatten_pattern ps')
    | PVar _ | PBool _ | PInt _ | POption None | PWild -> p
  in
  List.map (fun (p, e) -> (flatten_pattern p, flatten_exp e)) bs

  
let flatten_decl d =
  match d with
  | DLet (x, oty, e) -> DLet (x, Some (flatten_ty (oget oty)), flatten_exp e)
  | DMerge e -> DMerge (flatten_exp e)
  | DTrans e -> DTrans (flatten_exp e)
  | DInit e -> DInit (flatten_exp e)
  | DAssert e -> DAssert (flatten_exp e)
  | DRequire e -> DRequire (flatten_exp e)
  | DSymbolic (x, Exp e) -> DSymbolic (x, Exp (flatten_exp e))
  | DSymbolic (x, Ty ty) -> DSymbolic (x, Ty (flatten_ty ty))
  | DATy aty -> DATy (flatten_ty aty)
  | DNodes _ | DEdges _ -> d

let flatten ds = List.map flatten_decl ds
