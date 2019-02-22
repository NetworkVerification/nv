open Collections
open Syntax
open Slicing

(* Maps fresh names back to the original names *)
let map_back bmap new_name old_name =
  bmap := StringMap.add (Var.to_string new_name) (Var.to_string old_name) !bmap

let fresh x = Var.fresh (Var.to_string x)

let rec update_pattern (env: Var.t Env.t) (p: pattern) :
    pattern * Var.t Env.t =
  match p with
  | PWild | PBool _ | PInt _ -> (p, env)
  | PVar x ->
      let y = fresh x in
      (PVar y, Env.update env x y)
  | PTuple ps ->
      let env, ps = BatList.fold_left add_pattern (env, []) ps in
      (PTuple (BatList.rev ps), env)
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
  | EVar x -> evar (Env.lookup env x) |> wrap e
  | EVal v -> e
  | EOp (op, es) ->
      eop op (BatList.map (fun e -> alpha_convert_exp env e) es)
      |> wrap e
  | EFun f ->
      let x = fresh f.arg in
      let e' = alpha_convert_exp (Env.update env f.arg x) f.body in
      efun {f with arg= x; body= e'} |> wrap e
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
      let y = fresh x in
      let e2' = alpha_convert_exp (Env.update env x y) e2 in
      elet y e1' e2' |> wrap e
  | ETuple es ->
      etuple (BatList.map (fun e -> alpha_convert_exp env e) es)
      |> wrap e
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
      let y = fresh x in
      let env = Env.update env x y in
      let e = alpha_convert_exp env e in
      (env, DLet (y, tyo, e))
  | DSymbolic (x, Exp e) ->
      let y = fresh x in
      map_back bmap y x ;
      let env = Env.update env x y in
      let e = alpha_convert_exp env e in
      (env, DSymbolic (y, Exp e))
  | DSymbolic (x, Ty ty) ->
      (* let y = fresh x in *)
      (* map_back bmap x x ; *)
      let env = Env.update env x x in
      (env, DSymbolic (x, Ty ty))
  (* | DSymbolic (x, Ty ty) -> *)
  (*    let y = fresh x in *)
  (*    map_back bmap y x ; *)
  (*    let env = Env.update env x y in *)
  (*    (env, DSymbolic (y, Ty ty)) *)
  | DMerge e -> (env, DMerge (alpha_convert_exp env e))
  | DTrans e -> (env, DTrans (alpha_convert_exp env e))
  | DInit e -> (env, DInit (alpha_convert_exp env e))
  | DAssert e -> (env, DAssert (alpha_convert_exp env e))
  | DRequire e -> (env, DRequire (alpha_convert_exp env e))
  | DATy _ | DNodes _ | DEdges _ -> (env, d)
                                  
let rec alpha_convert_aux bmap env (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = alpha_convert_declaration bmap env d in
      d' :: alpha_convert_aux bmap env' ds'

let update_symbolics bmap smap =
  StringMap.fold
    (fun s v acc ->
      match StringMap.Exceptionless.find s bmap with
      | None -> StringMap.add s v acc
      | Some k -> StringMap.add k v acc )
    smap StringMap.empty

let adjust_solution bmap (s: Solution.t) =
  {s with symbolics= update_symbolics bmap s.symbolics}

let rec alpha_convert_declarations (ds: declarations) =
  Var.reset () ;
  let bmap = ref StringMap.empty in
  let prog = alpha_convert_aux bmap Env.empty ds in
  (prog, adjust_solution !bmap)

let alpha_convert_net net =
  Var.reset () ;
  let bmap = ref StringMap.empty in
  let env = Env.empty in
  let env, symbolics =
    BatList.fold_right (fun (x, ty_exp) (env, acc) ->
        match ty_exp with
        |  Exp e ->
            let y = fresh x in
            map_back bmap y x ;
            let env = Env.update env x y in
            let e = alpha_convert_exp env e in
            (env, (y, Exp e) :: acc)
        | Ty ty ->
           let env = Env.update env x x in
           (env, (x, Ty ty) :: acc)) net.symbolics (env, [])
  in
  let env, defs =
    BatList.fold_right (fun (x, tyo, exp) (env, acc) ->
        let y = fresh x in
        let env = Env.update env x y in
        let e = alpha_convert_exp env exp in
        (env, (y, tyo, e) :: acc)) net.defs (env, [])
  in
  let net' =
    { attr_type = net.attr_type;
      init = alpha_convert_exp env net.init;
      trans = alpha_convert_exp env net.trans;
      merge = alpha_convert_exp env net.merge;
      assertion = (match net.assertion with
                   | None -> None
                   | Some e -> Some (alpha_convert_exp env e));
      symbolics = symbolics;
      defs = defs;
      requires = BatList.map (alpha_convert_exp env) net.requires;
      graph = net.graph
    }
  in
  (net', adjust_solution !bmap)
  

module Tests =
  struct

    exception Duplicate
            
    let collect_unique_vars e =
      let vars = ref BatSet.empty in
      let checkCollect x =
        if BatSet.mem x !vars then
          raise Duplicate
        else
          vars := BatSet.add x !vars
      in
      Visitors.iter_exp (fun e ->
          match e.e with
          | EVar x -> checkCollect x
          | EFun f -> checkCollect f.arg
          | ELet (x, _, _) -> checkCollect x
          | _ -> ()) e;
      !vars

    let collect_vars e =
      let vars = ref [] in
      Visitors.iter_exp (fun e ->
          match e.e with
          | EVar x -> vars := x :: !vars
          | EFun f -> vars := f.arg :: !vars
          | ELet (x, _, _) -> vars := x :: !vars
          | _ -> ()) e;
      !vars
                            
    let alpha_exp_no_duplicates_prop env e =
      let aexp = alpha_convert_exp env e in
      try
        let _ = collect_unique_vars aexp in
        true
      with | Duplicate -> false
                        
    let alpha_exp_number_of_vars_prop env e =
      let aexp = alpha_convert_exp env e in
      try
        begin
          let avars = collect_unique_vars aexp in
          let vars = collect_vars e in
          BatList.length vars = BatSet.cardinal avars
        end
      with | Duplicate -> false

  end
