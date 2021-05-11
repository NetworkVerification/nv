open Syntax
open Batteries

let rec map_exp f (e : exp) =
  let e' = f e in
  let e' =
    match e'.e with
    | EVar _ | EVal _ -> e'
    | EOp (op, es) -> eop op (BatList.map (map_exp f) es)
    | EFun fn -> efun { fn with body = map_exp f fn.body }
    | EApp (e1, e2) -> eapp (map_exp f e1) (map_exp f e2)
    | EIf (e1, e2, e3) -> eif (map_exp f e1) (map_exp f e2) (map_exp f e3)
    | ELet (v, e1, e2) -> elet v (map_exp f e1) (map_exp f e2)
    | ETuple es -> etuple (BatList.map (map_exp f) es)
    | ESome e -> esome (map_exp f e)
    | EMatch (e, bs) ->
      ematch (map_exp f e) (mapBranches (fun (p, e) -> p, map_exp f e) bs)
    | ETy (e, t) -> ety (map_exp f e) t
    | ERecord map -> erecord (Collections.StringMap.map (fun e -> map_exp f e) map)
    | EProject (e, s) -> eproject (map_exp f e) s
  in
  aexp (e', e.ety, e.espan)
;;

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

let map_exp_decl f d =
  match d with
  | DLet (v, oty, e) -> DLet (v, oty, map_exp (f d) e)
  | DAssert e -> DAssert (map_exp (f d) e)
  | DPartition e -> DPartition (map_exp (f d) e)
  | DRequire e -> DRequire (map_exp (f d) e)
  | DSymbolic (v, Exp e) -> DSymbolic (v, Exp (map_exp (f d) e))
  | DSolve { aty; var_names; init; trans; merge; part } ->
    DSolve
      { aty
      ; var_names = map_exp (f d) var_names
      ; init = map_exp (f d) init
      ; trans = map_exp (f d) trans
      ; merge = map_exp (f d) merge
      ; part = Option.map (map_part (map_exp (f d))) part
      }
  | DNodes _ | DEdges _ | DSymbolic _ | DUserTy _ -> d
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
      | Some p -> fold_part List.cons p []
      | None -> []
    in
    List.iter (iter_exp (f d)) ([var_names; init; trans; merge] @ part_exps)
  | DNodes _ | DEdges _ | DSymbolic _ | DUserTy _ -> ()
;;

let rec map_exp_decls f ds = BatList.map (map_exp_decl f) ds
let rec iter_exp_decls f ds = BatList.iter (iter_exp_decl f) ds
