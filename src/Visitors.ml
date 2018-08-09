open Syntax

let rec iter_exp f (e: exp) =
  f e ;
  match e.e with
  | EVar _ | EVal _ -> ()
  | EOp (_, es) -> List.iter (iter_exp f) es
  | EFun {body= e} -> iter_exp f e
  | EApp (e1, e2) -> iter_exp f e1 ; iter_exp f e2
  | EIf (e1, e2, e3) -> iter_exp f e1 ; iter_exp f e2 ; iter_exp f e3
  | ELet (x, e1, e2) -> iter_exp f e1 ; iter_exp f e2
  | ETuple es -> List.iter (iter_exp f) es
  | ESome e -> iter_exp f e
  | EMatch (e, bs) ->
      iter_exp f e ;
      List.iter (fun (_, e) -> iter_exp f e) bs
  | ETy (e, _) -> iter_exp f e

let iter_exp_decl f d =
  match d with
  | DLet (_, _, e)
   |DMerge e
   |DTrans e
   |DInit e
   |DAssert e
   |DRequire e
   |DSymbolic (_, Exp e) ->
      iter_exp (f d) e
  | DATy _ | DNodes _ | DEdges _ | DSymbolic _ -> ()

let rec iter_exp_decls f ds = List.iter (iter_exp_decl f) ds
