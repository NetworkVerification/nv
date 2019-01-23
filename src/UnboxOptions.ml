open Collections
open Syntax


let rec empty_pattern ty =
  match ty with
  | TBool -> PWild
  | TInt size ->
     PWild
  | TTuple ts ->
     PTuple (BatList.map empty_pattern ts)
  | TOption _ ->
     PWild
  | TMap (ty1, ty2) ->
     PWild
  | TVar {contents= Link t} ->
     empty_pattern t
  | TVar _ | QVar _ | TArrow _ ->
     failwith ("internal error (empty_pattern)" ^ (Printing.ty_to_string ty))
   
let rec unbox_ty ty =
  match ty with
  | TVar {contents= Link t} -> unbox_ty t
  | TBool -> ty
  | TInt _ -> ty
  | TArrow (t1, t2) ->
     TArrow (unbox_ty t1, unbox_ty t2)
  | TTuple ts -> TTuple (BatList.map unbox_ty ts)
  | TOption t -> TTuple [TBool; (unbox_ty t)]
  | TMap (ty1, ty2) ->
     TMap (unbox_ty ty1, unbox_ty ty2)
  | QVar _ | TVar _ -> failwith "internal error (unbox_ty)"

let rec unbox_val v =
  match v.v with
  | VBool _ | VInt _ ->
     exp_of_value v
  | VOption None ->
     (match v.vty with
      | Some (TOption t) ->
         aexp (etuple [(vbool false |> exp_of_value); (default_exp_value (get_inner_type t))],
                 Some (unbox_ty (TOption t)), v.vspan)
     | _ -> failwith "expected option type")
  | VOption (Some v1) ->
     aexp (etuple [(vbool true |> exp_of_value); (unbox_val v1)],
           Some (unbox_ty (oget v.vty)), v.vspan)
  | VTuple vs ->
     aexp (etuple (BatList.map unbox_val vs), Some (unbox_ty (oget v.vty)), v.vspan)
  | VClosure _ -> failwith "Closures not yet implemented"
  | VMap _ -> failwith "no map values"
    
let rec unbox_exp e : exp =
  match e.e with
  | ETy (e, ty) -> unbox_exp e
  | EVal v ->
     unbox_val v
  | EVar _ -> aexp(e, Some (unbox_ty (oget e.ety)), e.espan)
  | EFun f ->
      aexp (efun
              { f with
                argty= Some (unbox_ty (oget f.argty));
                resty= Some (unbox_ty (oget f.resty));
                body= unbox_exp f.body },
            Some (unbox_ty (TArrow (oget f.argty, oget f.resty))), e.espan)
  | EApp (e1, e2) ->
     aexp (eapp (unbox_exp e1) (unbox_exp e2), Some (unbox_ty (oget e.ety)), e.espan)
  | EIf (e1, e2, e3) ->
     aexp (eif (unbox_exp e1) (unbox_exp e2) (unbox_exp e3),
           Some (unbox_ty (oget e.ety)), e.espan)
  | ELet (x, e1, e2) ->
     (* The commented piece of code is the correct way to do this
        transformation. The problem is I don't know how to do it in
        conjunction with tuple flattening *)
     (* (match (oget e1.ety) with *)
     (*  | TOption ty -> *)
     (*     aexp (ematch (unbox_exp e1) *)
     (*                  [(PTuple [PVar (proj_var 0 x); PVar (proj_var 1 x)], unbox_exp e2)], *)
     (*           Some (unbox_ty (oget e.ety)), e.espan) *)
     (*  | _ -> *)
     (*     aexp(elet x (unbox_exp e1) (unbox_exp e2), *)
  (*          Some (unbox_ty (oget e.ety)), e.espan)) *)
     aexp(elet x (unbox_exp e1) (unbox_exp e2),
          Some (unbox_ty (oget e.ety)), e.espan)
  | ETuple es ->
     aexp (etuple (BatList.map unbox_exp es), Some (unbox_ty (oget e.ety)), e.espan)
  | ESome e1 ->
     let p1 = aexp (e_val (vbool true), Some TBool, Span.default) in
     let p2 = aexp (unbox_exp e1, Some (unbox_ty (oget e1.ety)), Span.default) in
     aexp (etuple [p1;p2], Some (unbox_ty (oget e.ety)), Span.default)
  | EMatch (e1, bs) ->
     (* Printf.printf "match expr: %s" (Printing.exp_to_string e); *)
     aexp (ematch (unbox_exp e1) (unbox_branches bs (oget e1.ety)),
           Some (unbox_ty (oget e.ety)),
           e.espan)
  | EOp (op, es) -> (
    match (op, es) with
    | And, _
    | Or, _
    | Not, _
    | UAdd _, _
    | USub _, _
    | UEq, _
    | ULess _, _
    | AtMost _, _
    | ULeq _, _
    | MCreate, _
    | MGet, _
    | MSet, _ ->
       aexp (eop op (BatList.map unbox_exp es),
             Some (unbox_ty (oget e.ety)), e.espan)
    | _ -> failwith "TODO: implement option unboxing for rest of map operations")
                  
and unbox_branches bs ty =
  let rec unbox_pattern p ty =
    let ty = get_inner_type ty in
    match p with
    | POption None ->
       (match ty with
        | TOption t ->
           let ps = empty_pattern t in
           PTuple [(PBool false);ps]
        | _ ->
           failwith "must match on option type")
    | POption (Some p) ->
       (match ty with
        | TOption t ->
           PTuple [(PBool true); unbox_pattern p t]
        | _ ->
           failwith "must match on option type")
    | PTuple ps ->
       (match ty with
        | TTuple ts ->
           PTuple (BatList.map2 unbox_pattern ps ts)
        | _ ->
           failwith "must match on a tuple type")
    | PVar x ->
       (match ty with
        | TOption t -> p
           (* PTuple [PVar (proj_var 0 x); PVar (proj_var 1 x)] *)
        | _ -> p)
    | _ -> p
  in
  BatList.map (fun (p, e) -> (unbox_pattern p ty, unbox_exp e)) bs

let unbox_decl d =
  match d with
  | DLet (x, oty, e) -> DLet (x, Some (unbox_ty (oget oty)), unbox_exp e)
  | DMerge e -> DMerge (unbox_exp e)
  | DTrans e ->
     DTrans (unbox_exp e)
  | DInit e ->
     (* Printf.printf "init ty:%s\n" (Syntax.show_exp ~show_meta:true e); *)
     DInit (unbox_exp e)
  | DAssert e -> DAssert (unbox_exp e)
  | DRequire e -> DRequire (unbox_exp e)
  | DSymbolic (x, Exp e) -> DSymbolic (x, Exp (unbox_exp e))
  | DSymbolic (x, Ty ty) -> DSymbolic (x, Ty (unbox_ty ty))
  | DATy aty -> DATy (unbox_ty aty)
  | DNodes _ | DEdges _ -> d

let unbox ds = BatList.map unbox_decl ds
