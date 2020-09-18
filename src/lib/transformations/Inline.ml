open Nv_lang.Syntax
open Nv_datastructures
open Nv_lang.Collections

let is_function_ty e =
  match get_inner_type (Nv_utils.OCamlUtils.oget e.ety) with
  | TArrow _ -> true
  | _ -> false
;;

let rec has_var p x =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PNode _ -> false
  | PVar y -> Var.equals x y
  | PEdge (p1, p2) -> has_var p1 x || has_var p2 x
  | PTuple ps -> BatList.exists (fun p -> has_var p x) ps
  | PRecord map -> StringMap.exists (fun _ p -> has_var p x) map
  | POption None -> false
  | POption (Some p) -> has_var p x
;;

let rec remove_all env p =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PNode _ -> env
  | PVar x -> Env.remove env x
  | PEdge (p1, p2) -> remove_all env (PTuple [p1; p2])
  | PTuple ps -> BatList.fold_left (fun acc p -> remove_all acc p) env ps
  | PRecord map -> StringMap.fold (fun _ p acc -> remove_all acc p) map env
  | POption None -> env
  | POption (Some p) -> remove_all env p
;;

let rec substitute x e1 e2 =
  match e1.e with
  | EVar y -> if Var.equals x y then e2 else e1
  | EFun f ->
    if Var.equals x f.arg
    then e1
    else efun { f with body = substitute x f.body e2 } |> wrap e1
  | EApp (e3, e4) -> eapp (substitute x e3 e2) (substitute x e4 e2) |> wrap e1
  | EIf (e3, e4, e5) ->
    eif (substitute x e3 e2) (substitute x e4 e2) (substitute x e5 e2)
    |> wrap e1
  | ELet (y, e3, e4) ->
    if Var.equals x y
    then elet y (substitute x e3 e2) e4
    else elet y (substitute x e3 e2) (substitute x e4 e2) |> wrap e1
  | ETy (e1, ty) -> ety (substitute x e1 e2) ty |> wrap e1
  | EMatch (e, bs) ->
    ematch
      (substitute x e e2)
      (mapBranches (fun (p, e) -> substitute_pattern x e2 (p, e)) bs)
    |> wrap e1
  | ESome e -> esome (substitute x e e2) |> wrap e1
  | ETuple es -> etuple (BatList.map (fun e -> substitute x e e2) es) |> wrap e1
  | ERecord map ->
    erecord (StringMap.map (fun e -> substitute x e e2) map) |> wrap e1
  | EProject (e, l) -> eproject (substitute x e e2) l
  | EOp (op, es) ->
    eop op (BatList.map (fun e -> substitute x e e2) es) |> wrap e1
  | EVal _ -> e1

and substitute_pattern x e2 (p, e) =
  if has_var p x then p, e else p, substitute x e e2
;;

let rec inline_app env e1 e2 : exp =
  let exp =
    match e1.e with
    | EVar x ->
      (match Env.lookup_opt env x with
      | None -> eapp e1 e2 |> wrap e1
      | Some e -> inline_app env e e2)
    | EFun f ->
      let e = substitute f.arg f.body e2 in
      inline_exp env e
    | EIf (e3, e4, e5) ->
      let etrue = inline_app env e4 e2 in
      let efalse = inline_app env e5 e2 in
      eif e3 etrue efalse |> wrap e1
    | ELet (x, e3, e4) ->
      let e5 = inline_exp env (eapp e4 e2 |> wrap e4) in
      elet x e3 e5 |> wrap e1
    | ETy (e1, _) -> inline_app env e1 e2
    | EMatch (e, bs) ->
      let e = inline_exp env e in
      let branches =
        mapBranches (fun (p, e) -> inline_branch_app env e2 (p, e)) bs
      in
      ematch e branches |> wrap e1
    | EApp _ -> eapp e1 e2 |> wrap e1
    | ESome _ | ETuple _ | EOp _ | EVal _ | ERecord _ | EProject _ ->
      failwith
        (Printf.sprintf "inline_app: %s" (Nv_lang.Printing.exp_to_string e1))
  in
  (* Printf.printf "inline_app e1: %s\ninline_app e2: %s)\n"
     (Printing.exp_to_string e1)
     (Printing.exp_to_string e2) ;
     Printf.printf "result: %s\n\n" (Printing.exp_to_string exp); *)
  exp

and inline_branch_app env e2 (p, e) = p, inline_app env e e2

and inline_exp (env : exp Env.t) (e : exp) : exp =
  match e.e with
  | EVar x ->
    (match Env.lookup_opt env x with
    | None -> e
    | Some e1 -> e1)
  | EVal _ -> e
  | EOp (op, es) -> eop op (BatList.map (inline_exp env) es) |> wrap e
  | EFun f ->
    let body = inline_exp env f.body in
    efun { f with body } |> wrap e
  | EApp (e1, e2) -> inline_app env (inline_exp env e1) (inline_exp env e2)
  | EIf (e1, e2, e3) ->
    eif (inline_exp env e1) (inline_exp env e2) (inline_exp env e3) |> wrap e
  | ELet (x, e1, e2) ->
    let e1' = inline_exp env e1 in
    (* (match e1.ety with *)
    (* | None -> Printf.printf "no type\n"; *)
    (* | Some ty -> *)
    (*    Printf.printf "crashes here: %s\n" (Printing.ty_to_string ty)); *)
    (* Printf.printf "crashes here: %s\n" (Printing.exp_to_string e1); *)
    if is_function_ty e1
    then inline_exp (Env.update env x e1') e2
    else elet x e1' (inline_exp env e2) |> wrap e
  | ETuple es -> etuple (BatList.map (inline_exp env) es) |> wrap e
  | ERecord map -> erecord (StringMap.map (inline_exp env) map) |> wrap e
  | EProject (e, l) -> eproject (inline_exp env e) l |> wrap e
  | ESome e1 -> esome (inline_exp env e1) |> wrap e
  | EMatch (e1, bs) ->
    ematch
      (inline_exp env e1)
      (mapBranches (fun (p, e) -> inline_branch env (p, e)) bs)
    |> wrap e
  | ETy (e1, ty) -> ety (inline_exp env e1) ty |> wrap e

(* Printf.printf "inline: %s\n" (Printing.exp_to_string e);
   Printf.printf "result: %s\n\n" (Printing.exp_to_string ret); *)

(* TODO: right now this is assuming that patterns won't contain functions
   this will fail for example with an expression like:  Some (fun v -> v) *)
and inline_branch env (p, e) =
  let env' = remove_all env p in
  p, inline_exp env' e
;;

let inline_declaration (env : exp Env.t) (d : declaration) =
  match d with
  | DLet (x, _, e) ->
    let e = inline_exp env e in
    (* TODO: always inline? check size of exp? *)
    Env.update env x e, None
  (* if is_function_ty e then (Env.update env x e, None) *)
  (* else (env, Some (DLet (x, tyo, e))) *)
  | DSymbolic (x, e) ->
    (* Inline in symbolic expression but do not inline the symbolic expression!
       It is only used in the case of the simulator *)
    (match e with
    | Exp e' ->
      let e' = inline_exp env e' in
      env, Some (DSymbolic (x, Exp e'))
    | Ty _ -> env, Some (DSymbolic (x, e)))
  | DAssert e -> env, Some (DAssert (inline_exp env e))
  | DSolve { aty; var_names; init; trans; merge } ->
    (* Like with symbolics, inline within the functions but don't inline e in future expressions *)
    let init, trans, merge =
      inline_exp env init, inline_exp env trans, inline_exp env merge
    in
    env, Some (DSolve { aty; var_names; init; trans; merge })
  | DPartition e -> env, Some (DPartition (inline_exp env e)) (* partitioning *)
  | DInterface e -> env, Some (DInterface (inline_exp env e)) (* partitioning *)
  | DRequire e -> env, Some (DRequire (inline_exp env e))
  | DUserTy _ | DNodes _ | DEdges _ -> env, Some d
;;

let rec inline_declarations_aux env (ds : declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
    let env', d' = inline_declaration env d in
    (match d' with
    | None -> inline_declarations_aux env' ds'
    | Some d' -> d' :: inline_declarations_aux env' ds')
;;

let inline_declarations (ds : declarations) =
  inline_declarations_aux Env.empty ds
;;

(* match get_attr_type ds with
   | None ->
   failwith "attribute type not declared: type attribute = ..."
   | Some ty -> inline_declarations_aux Env.empty ds *)
