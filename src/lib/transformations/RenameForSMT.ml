open Nv_lang
open Nv_datastructures
open Syntax
open Collections

(* A program transformation that prepends every symbolic variable with the prefix
   "symbolic-" and every solution variable with "solve-". Leaves other variables
   untouched. SMT expects this to have been run, and uses the prefixes during
   model parsing (SmtModel.ml). *)

(* Maps fresh names back to the original names *)
let map_back bmap new_name old_name =
  bmap := Collections.VarMap.add new_name old_name !bmap

let fresh_solve x = Var.fresh ("solve-" ^ Var.name x)
let fresh_symbolic x = Var.fresh ("symbolic-" ^ Var.name x)

let rec rename_solve_vars bmap env e =
  match e.e with
  | EVar x ->
    let y = fresh_solve x in
    map_back bmap y x ;
    let env = Env.update env x y in
    env, evar y |> wrap e
  | ETuple es ->
    let env', es' =
      List.fold_left
        (fun (env, acc) e -> let env', y = rename_solve_vars bmap env e in env', y :: acc)
        (env, []) es
    in
    env', etuple (List.rev es') |> wrap e
  | _ -> failwith "Bad DSolve"

let rec update_pattern (env: Var.t Env.t) (p: pattern) :
  pattern * Var.t Env.t =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PNode _ | PVar _ -> (p, env)
  | PEdge (p1, p2) ->
    let p1', env = update_pattern env p1 in
    let p2', env = update_pattern env p2 in
    PEdge (p1', p2'), env
  | PTuple ps ->
    let env, ps = BatList.fold_left add_pattern (env, []) ps in
    (PTuple (BatList.rev ps), env)
  | PRecord map ->
    let env, map =
      StringMap.fold
        (fun k p (env, acc) ->
           let p', env' = update_pattern env p in
           env', StringMap.add k p' acc)
        map
        (env, StringMap.empty)
    in
    (PRecord map, env)
  | POption None -> (p, env)
  | POption (Some p) ->
    let p', env = update_pattern env p in
    (POption (Some p'), env)

and add_pattern (env, ps) p =
  let p', env' = update_pattern env p in
  (env', p' :: ps)

let rec alpha_convert_exp (env: Var.t Env.t) (e: exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e);
     Printf.printf "type: %s\n" (Printing.ty_to_string (oget e.ety)); *)
  match e.e with
  | EVar x ->
    (match Env.lookup_opt env x with
     | None -> e
     | Some x -> evar x)
    |> wrap e
  | EVal _ -> e
  | EOp (op, es) ->
    eop op (BatList.map (fun e -> alpha_convert_exp env e) es)
    |> wrap e
  | EFun f ->
    let e' = alpha_convert_exp env f.body in
    efun {f with body = e'} |> wrap e
  | EApp (e1, e2) ->
    eapp (alpha_convert_exp env e1) (alpha_convert_exp env e2)
    |> wrap e
  | EIf (e1, e2, e3) ->
    eif
      (alpha_convert_exp env e1)
      (alpha_convert_exp env e2)
      (alpha_convert_exp env e3)
    |> wrap e
  | ELet (x, e1, e2) ->
    let e1' = alpha_convert_exp env e1 in
    let e2' = alpha_convert_exp env e2 in
    elet x e1' e2' |> wrap e
  | ETuple es ->
    etuple (BatList.map (fun e -> alpha_convert_exp env e) es)
    |> wrap e
  | ERecord map ->
    erecord (StringMap.map (fun e -> alpha_convert_exp env e) map)
    |> wrap e
  | EProject (e, l) ->
    eproject (alpha_convert_exp env e) l |> wrap e
  | ESome e1 -> esome (alpha_convert_exp env e1) |> wrap e
  | EMatch (e1, bs) ->
    let bs' =
      mapBranches (fun (p, ep) ->
          let p, env = update_pattern env p in
          (p, alpha_convert_exp env ep)) bs
    in
    ematch (alpha_convert_exp env e1) bs' |> wrap e
  | ETy (e1, ty) -> ety (alpha_convert_exp env e1) ty |> wrap e

let alpha_convert_declaration bmap (env: Var.t Env.t)
    (d: declaration) =
  match d with
  | DLet (x, tyo, e) ->
    let e = alpha_convert_exp env e in
    (env, DLet (x, tyo, e))
  | DSymbolic (x, Exp e) ->
    let y = fresh_symbolic x in
    map_back bmap y x ;
    let env = Env.update env x y in
    let e = alpha_convert_exp env e in
    (env, DSymbolic (y, Exp e))
  | DSymbolic (x, Ty ty) ->
    let y = fresh_symbolic x in
    map_back bmap y x ;
    let env = Env.update env x y in
    (env, DSymbolic (y, Ty ty))
  | DSolve {aty; var_names; init; trans; merge} ->
    let init, trans, merge =
      alpha_convert_exp env init, alpha_convert_exp env trans, alpha_convert_exp env merge
    in
    let env, y = rename_solve_vars bmap env var_names in
    (env, DSolve {aty; var_names = y; init; trans; merge})
  | DAssert e -> (env, DAssert (alpha_convert_exp env e))
  | DPartition e -> (env, DPartition (alpha_convert_exp env e)) (* partitioning *)
  | DInterface e -> (env, DInterface (alpha_convert_exp env e)) (* partitioning *)
  | DRequire e -> (env, DRequire (alpha_convert_exp env e))
  | DUserTy _ | DNodes _ | DEdges _ -> (env, d)

let rec alpha_convert_aux bmap env (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
    let env', d' = alpha_convert_declaration bmap env d in
    d' :: alpha_convert_aux bmap env' ds'

let update_symbolics bmap smap =
  let open Collections in
  VarMap.fold
    (fun s v acc ->
       match VarMap.Exceptionless.find s bmap with
       | None -> VarMap.add s v acc
       | Some k -> VarMap.add k v acc )
    smap VarMap.empty

let adjust_solution bmap (s: Nv_solution.Solution.t) =
  {s with symbolics= update_symbolics bmap s.symbolics;
          solves = update_symbolics bmap s.solves}

let rec rename_declarations (ds: declarations) =
  (* Var.reset () ; *)
  let bmap = ref Collections.VarMap.empty in
  let prog = alpha_convert_aux bmap Env.empty ds in
  (prog, adjust_solution !bmap)

let rename_net net =
  let bmap = ref Collections.VarMap.empty in
  let env = Env.empty in
  let env, symbolics =
    BatList.fold_right (fun (x, ty_exp) (env, acc) ->
        let y = fresh_symbolic x in
        map_back bmap y x ;
        let env = Env.update env x y in
        match ty_exp with
        |  Exp e ->
          let e = alpha_convert_exp env e in
          (env, (y, Exp e) :: acc)
        | Ty ty ->
          (env, (y, Ty ty) :: acc))
      net.symbolics (env, [])
  in
  let env, defs =
    BatList.fold_right (fun (x, tyo, exp) (env, acc) ->
        let e = alpha_convert_exp env exp in
        (env, (x, tyo, e) :: acc)) net.defs (env, [])
  in
  let env, solves =
    BatList.fold_right (fun {aty; var_names; init; trans; merge} (env, acc) ->
        let init, trans, merge =
          alpha_convert_exp env init, alpha_convert_exp env trans, alpha_convert_exp env merge
        in
        let env, y = rename_solve_vars bmap env var_names in
        (env, {aty; var_names = y; init; trans; merge} :: acc)) net.solves (env, [])
  in
  let net' =
    { attr_type = net.attr_type;
      init = alpha_convert_exp env net.init;
      trans = alpha_convert_exp env net.trans;
      merge = alpha_convert_exp env net.merge;
      assertion = (match net.assertion with
          | None -> None
          | Some e -> Some (alpha_convert_exp env e));
      solves = solves;
      (* partitioning *)
      partition = (match net.partition with
          | None -> None
          | Some e -> Some (alpha_convert_exp env e));
      interface = (match net.interface with
          | None -> None
          | Some e -> Some (alpha_convert_exp env e));
      (* end partitioning *)
      symbolics = symbolics;
      defs = defs;
      utys = net.utys;
      requires = BatList.map (alpha_convert_exp env) net.requires;
      graph = net.graph
    }
  in
  (net', adjust_solution !bmap)

let rename_srp (srp : Syntax.srp_unfold) =
  let bmap = ref Collections.VarMap.empty in
  let env = Env.empty in
  let env, symbolics =
    BatList.fold_right (fun (x, ty_exp) (env, acc) ->
        let y = fresh_symbolic x in
        map_back bmap y x ;
        let env = Env.update env x y in
        match ty_exp with
        |  Exp e ->
          let e = alpha_convert_exp env e in
          (env, (y, Exp e) :: acc)
        | Ty ty ->
          (env, (y, Ty ty) :: acc))
      srp.srp_symbolics (env, [])
  in
  let env = AdjGraph.VertexMap.fold (fun _ xs env ->
      BatList.fold_right (fun (x, _) env ->
          Env.update env x x) xs env) srp.srp_labels env
  in
  let srp' =
    (* TODO: add partitioning? *)
    { srp_attr = srp.srp_attr;
      srp_constraints = AdjGraph.VertexMap.map (alpha_convert_exp env) srp.srp_constraints;
      srp_labels = srp.srp_labels;
      srp_assertion = (match srp.srp_assertion with
          | None -> None
          | Some e -> Some (alpha_convert_exp env e));
      srp_symbolics = symbolics;
      srp_requires = BatList.map (alpha_convert_exp env) srp.srp_requires;
      srp_graph = srp.srp_graph
    }
  in
  (srp', adjust_solution !bmap)
