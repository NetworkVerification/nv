open Syntax
open Batteries

let rec iter_exp f (e : exp) =
  f e;
  match e.e with
  | EVar _ | EVal _ -> ()
  | EOp (_, es) -> BatList.iter (iter_exp f) es
  | EFun { body = e } -> iter_exp f e
  | EApp (e1, e2) ->
    iter_exp f e1;
    iter_exp f e2
  | EIf (e1, e2, e3) ->
    iter_exp f e1;
    iter_exp f e2;
    iter_exp f e3
  | ELet (_, e1, e2) ->
    iter_exp f e1;
    iter_exp f e2
  | ETuple es -> BatList.iter (iter_exp f) es
  | ESome e -> iter_exp f e
  | EMatch (e, bs) ->
    iter_exp f e;
    iterBranches (fun (_, e) -> iter_exp f e) bs
  | ETy (e, _) -> iter_exp f e
  | ERecord map -> Collections.StringMap.iter (fun _ -> f) map
  | EProject (e, _) -> iter_exp f e
;;

let iter_exp_decl f d =
  match d with
  | DLet (_, _, e)
  | DAssert e
  | DPartition e (* partitioning *)
  | DRequire e
  | DSymbolic (_, Exp e) -> iter_exp (f d) e
  | DSolve { var_names; init; trans; merge; part; _ } ->
    let part_exps =
      match part with
      | Some { interface; decomp = (lt, rt); global } ->
        let ocons o = Option.apply (Option.map List.cons o) in
        ocons global (ocons rt (ocons lt [interface]))
      | None -> []
    in
    List.iter (iter_exp (f d)) ([var_names; init; trans; merge] @ part_exps)
  | DNodes _ | DEdges _ | DSymbolic _ | DUserTy _ -> ()
;;

let rec iter_exp_decls f ds = BatList.iter (iter_exp_decl f) ds
