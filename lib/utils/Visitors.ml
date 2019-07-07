open Syntax
   
let rec iter_exp f (e: exp) =
  f e ;
  match e.e with
  | EVar _ | EVal _ -> ()
  | EOp (_, es) -> BatList.iter (iter_exp f) es
  | EFun {body= e; _} -> iter_exp f e
  | EApp (e1, e2) -> iter_exp f e1 ; iter_exp f e2
  | EIf (e1, e2, e3) -> iter_exp f e1 ; iter_exp f e2 ; iter_exp f e3
  | ELet (_x, e1, e2) -> iter_exp f e1 ; iter_exp f e2
  | ETuple es -> BatList.iter (iter_exp f) es
  | ESome e -> iter_exp f e
  | EMatch (e, bs) ->
     iter_exp f e ;
     iterBranches (fun (_, e) -> iter_exp f e) bs
  | ETy (e, _) -> iter_exp f e
  | ERecord map -> RecordUtils.StringMap.iter (fun _ -> f) map
  | EProject (e,_) -> iter_exp f e

let iter_exp_decl f d =
  match d with
  | DLet (_, _, e)
   |DMerge e
   |DTrans e
   |DInit e
   |DAssert e
   |DPartition e (* partitioning *)
   |DInterface e (* partitioning *)
   |DRequire e
   |DSymbolic (_, Exp e) ->
      iter_exp (f d) e
  | DATy _ | DNodes _ | DEdges _ | DSymbolic _ | DUserTy _ -> ()

let rec iter_exp_decls f ds = BatList.iter (iter_exp_decl f) ds

let iter_exp_net f (net : Syntax.network) =
  BatList.iter (fun (_,_,e) -> iter_exp f e) net.defs;
  BatList.iter (fun (_,e) ->
      match e with
      | Exp e -> iter_exp f e
      | _ -> ()) net.symbolics;
  iter_exp f net.merge;
  iter_exp f net.trans;
  iter_exp f net.init;
  (match net.assertion with
   | Some e -> iter_exp f e
   | None -> ());
  BatList.iter (fun e -> iter_exp f e) net.requires
  
