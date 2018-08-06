open Syntax

let is_function_ty e =
  match Typing.get_inner_type (oget e.ety) with TArrow _ -> true | _ -> false

let annot ty e = {e= e.e; ety= Some ty; espan= e.espan}

let rec has_var p x =
  match p with
  | PWild | PBool _ | PUInt32 _ -> false
  | PVar y -> Var.equals x y
  | PTuple ps -> List.fold_left (fun acc p -> acc || has_var p x) false ps
  | POption None -> false
  | POption (Some p) -> has_var p x

let rec remove_all env p =
  match p with
  | PWild | PBool _ | PUInt32 _ -> env
  | PVar x -> Env.remove env x
  | PTuple ps -> List.fold_left (fun acc p -> remove_all acc p) env ps
  | POption None -> env
  | POption (Some p) -> remove_all env p

let rec substitute x e1 e2 =
  match e1.e with
  | EVar y -> if Var.equals x y then e2 else e1
  | EFun f ->
      if Var.equals x f.arg then e1
      else EFun {f with body= substitute x f.body e2} |> wrap e1
  | EApp (e3, e4) -> EApp (substitute x e3 e2, substitute x e4 e2) |> wrap e1
  | EIf (e3, e4, e5) ->
      EIf (substitute x e3 e2, substitute x e4 e2, substitute x e5 e2)
      |> wrap e1
  | ELet (y, e3, e4) ->
      if Var.equals x y then e1
      else ELet (x, substitute x e3 e2, substitute x e4 e2) |> wrap e1
  | ETy (e1, ty) -> ETy (substitute x e1 e2, ty) |> wrap e1
  | EMatch (e, bs) ->
      EMatch (substitute x e e2, List.map (substitute_pattern x e2) bs)
      |> wrap e1
  | ESome e -> ESome (substitute x e e2) |> wrap e1
  | ETuple es -> ETuple (List.map (fun e -> substitute x e e2) es) |> wrap e1
  | EOp (op, es) ->
      EOp (op, List.map (fun e -> substitute x e e2) es) |> wrap e1
  | EVal _ -> e1

and substitute_pattern x e2 (p, e) =
  if has_var p x then (p, e) else (p, substitute x e e2)

let inst_types t1 t2 =
  let map = ref Env.empty in
  let rec aux t1 t2 =
    match (t1, t2) with
    | TVar {contents= Link r}, s | r, TVar {contents= Link s} -> aux r s
    | QVar x, t | TVar {contents= Unbound (x, _)}, t ->
        map := Env.update !map x t
    | TBool, TBool -> ()
    | TInt i, TInt j when i = j -> ()
    | TArrow (r1, s1), TArrow (r2, s2) -> aux r1 r2 ; aux s1 s2
    | TTuple ts1, TTuple ts2 when List.length ts1 = List.length ts2 ->
        List.combine ts1 ts2 |> List.iter (fun (r, s) -> aux r s)
    | TOption r, TOption s -> aux r s
    | _ ->
        Console.error
          (Printf.sprintf "unimplemented (inst_types): (%s, %s)"
             (Printing.ty_to_string t1) (Printing.ty_to_string t2))
  in
  aux t1 t2 ; !map

let rec inline_type (env: ty Env.t) ty : ty =
  match ty with
  | TVar {contents= Link t} -> inline_type env t
  | QVar x | TVar {contents= Unbound (x, _)} -> (
    match Env.lookup_opt env x with Some t -> t | None -> ty )
  | TBool | TInt _ -> ty
  | TArrow (r, s) -> TArrow (inline_type env r, inline_type env s)
  | TTuple ts -> TTuple (List.map (inline_type env) ts)
  | TOption r -> TOption (inline_type env r)
  | _ -> Console.error "unimplemented (inline_type)"

let inline_type_app e1 e2 : ty =
  match (Typing.get_inner_type (oget e1.ety), oget e2.ety) with
  | TArrow (t1, t2), t3 ->
      let env = inst_types t1 t3 in
      inline_type env t2
  | _ -> Console.error "inlining internals (inline_type_app)"

(* match get_inner_type (oget ty) with
  | TArrow (_, t2) -> t2
  | _ -> Console.error "inlining internals: %s\n" *)

let rec inline_app env e1 e2 : exp =
  (* Printf.printf "inline_app e1: %s\ninline_app e2: %s)\n"
    (Printing.exp_to_string e1)
    (Printing.exp_to_string e2) ; *)
  let exp =
    match e1.e with
    | EVar x -> (
      match Env.lookup_opt env x with
      | None -> EApp (e1, e2) |> wrap e1 |> annot (inline_type_app e1 e2)
      | Some e -> inline_app env e e2 )
    | EFun f ->
        let e = substitute f.arg f.body e2 |> annot (oget f.resty) in
        inline_exp env e
    | EIf (e3, e4, e5) ->
        let etrue = inline_app env e4 e2 in
        let efalse = inline_app env e5 e2 in
        EIf (e3, etrue, efalse) |> wrap e1 |> annot (oget etrue.ety)
    | ELet (x, e3, e4) ->
        let e5 =
          inline_exp env
            (EApp (e4, e2) |> wrap e4 |> annot (inline_type_app e4 e2))
        in
        ELet (x, e3, e5) |> wrap e1
    | ETy (e1, ty) -> inline_app env e1 e2
    | EMatch (e, bs) -> (
        let e = inline_exp env e in
        let branches = List.map (inline_branch_app env e2) bs in
        let e = EMatch (e, branches) |> wrap e1 in
        match branches with
        | [] -> Console.error "internal error"
        | (p, eb) :: _ -> e |> annot (oget eb.ety) )
    | EApp _ -> EApp (e1, e2) |> wrap e1 |> annot (inline_type_app e1 e2)
    | ESome _ | ETuple _ | EOp _ | EVal _ ->
        Console.error
          (Printf.sprintf "inline_app: %s" (Printing.exp_to_string e1))
  in
  exp

and inline_branch_app env e2 (p, e) = (p, inline_app env e e2)

and inline_exp (env: exp Env.t) (e: exp) : exp =
  match e.e with
  | EVar x -> ( match Env.lookup_opt env x with None -> e | Some e1 -> e1 )
  | EVal v -> e
  | EOp (op, es) -> EOp (op, List.map (inline_exp env) es) |> wrap e
  | EFun f ->
      let body = inline_exp env f.body in
      EFun {f with body} |> wrap e
  | EApp (e1, e2) -> inline_app env (inline_exp env e1) (inline_exp env e2)
  | EIf (e1, e2, e3) ->
      EIf (inline_exp env e1, inline_exp env e2, inline_exp env e3) |> wrap e
  | ELet (x, e1, e2) ->
      let e1' = inline_exp env e1 in
      if is_function_ty e1 then inline_exp (Env.update env x e1') e2
      else ELet (x, e1', inline_exp env e2) |> wrap e
  | ETuple es -> ETuple (List.map (inline_exp env) es) |> wrap e
  | ESome e1 -> ESome (inline_exp env e1) |> wrap e
  | EMatch (e1, bs) ->
      EMatch (inline_exp env e1, List.map (inline_branch env) bs) |> wrap e
  | ETy (e1, ty) -> ETy (inline_exp env e1, ty) |> wrap e

(* TODO: right now this is assuming that patterns won't contain functions
   this will fail for example with an expression like:  Some (fun v -> v) *)
and inline_branch env (p, e) =
  let env' = remove_all env p in
  (p, inline_exp env' e)

let inline_declaration (env: exp Env.t) (d: declaration) =
  match d with
  | DLet (x, tyo, e) ->
      if is_function_ty e then (Env.update env x e, None)
      else (env, Some (DLet (x, tyo, e)))
  | DSymbolic (x, e) -> (env, Some (DSymbolic (x, e)))
  | DMerge e -> (env, Some (DMerge (inline_exp env e)))
  | DTrans e -> (env, Some (DTrans (inline_exp env e)))
  | DInit e -> (env, Some (DInit (inline_exp env e)))
  | DATy _ | DNodes _ | DEdges _ -> (env, Some d)

let rec inline_declarations (ds: declarations) =
  match get_attr_type ds with
  | None -> Console.error "attribute type not declared: type attribute = ..."
  | Some ty -> inline_declarations_aux Env.empty ds

and inline_declarations_aux env (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = inline_declaration env d in
      match d' with
      | None -> inline_declarations_aux env' ds'
      | Some d' -> d' :: inline_declarations_aux env' ds'
