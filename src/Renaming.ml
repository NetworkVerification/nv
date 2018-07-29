open Syntax

let fresh x = Var.fresh (Var.to_string x)

let wrap exp e = {e; ety= exp.ety; espan= exp.espan}

let rec update_pattern (env: Var.t Env.t) (p: pattern) : Var.t Env.t =
  match p with
  | PWild | PBool _ | PUInt32 _ -> env
  | PVar v -> Env.update env v (fresh v)
  | PTuple ps -> List.fold_left (fun acc p -> update_pattern acc p) env ps
  | POption None -> env
  | POption Some p -> update_pattern env p


let rec alpha_convert_exp (env: Var.t Env.t) (e: exp) =
  match e.e with
  | EVar x -> EVar (Env.lookup env x) |> wrap e
  | EVal v -> e
  | EOp (op, es) ->
      EOp (op, List.map (fun e -> alpha_convert_exp env e) es) |> wrap e
  | EFun f ->
      let x = fresh f.arg in
      let e' = alpha_convert_exp (Env.update env f.arg x) f.body in
      EFun {f with arg= x; body= e'} |> wrap e
  | EApp (e1, e2) ->
      EApp (alpha_convert_exp env e1, alpha_convert_exp env e2) |> wrap e
  | EIf (e1, e2, e3) ->
      EIf
        ( alpha_convert_exp env e1
        , alpha_convert_exp env e2
        , alpha_convert_exp env e3 )
      |> wrap e
  | ELet (x, e1, e2) ->
      let e1' = alpha_convert_exp env e1 in
      let y = fresh x in
      let e2' = alpha_convert_exp (Env.update env x y) e2 in
      ELet (y, e1', e2') |> wrap e
  | ETuple es ->
      ETuple (List.map (fun e -> alpha_convert_exp env e) es) |> wrap e
  | EProj (i, e1) -> EProj (i, alpha_convert_exp env e1) |> wrap e
  | ESome e1 -> ESome (alpha_convert_exp env e1) |> wrap e
  | EMatch (e, bs) ->
      let bs' =
        List.map
          (fun (p, e) -> (p, alpha_convert_exp (update_pattern env p) e))
          bs
      in
      EMatch (alpha_convert_exp env e, bs') |> wrap e
  | ETy (e1, ty) -> alpha_convert_exp env e1


let alpha_convert_declaration (env: Var.t Env.t) (d: declaration) =
  match d with
  | DLet (x, tyo, e) ->
      let env = Env.update env x (fresh x) in
      let e = alpha_convert_exp env e in
      (env, DLet (x, tyo, e))
  | DMerge e -> (env, DMerge (alpha_convert_exp env e))
  | DTrans e -> (env, DTrans (alpha_convert_exp env e))
  | DInit e -> (env, DInit (alpha_convert_exp env e))
  | DATy _ | DNodes _ | DEdges _ -> (env, d)


let rec alpha_convert_aux env (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = alpha_convert_declaration env d in
      d' :: alpha_convert_aux env' ds'


let rec alpha_convert_declarations (ds: declarations) =
  alpha_convert_aux Env.empty ds
