(* Type inference with efficient generalization via levels; 
 * code following http://okmij.org/ftp/ML/generalization.html#levels 
 *)

open Syntax
open Printing

let debug = true

let if_debug s = if debug then print_endline s else ()

exception Inference of string

let error s = raise (Inference s)

let oget (x: 'a option) : 'a =
  match x with None -> failwith "oget" | Some y -> y


let node_ty = tint

let edge_ty = TTuple [node_ty; node_ty]

let init_ty aty = TArrow (node_ty, aty)

let merge_ty aty = TArrow (node_ty, TArrow (aty, TArrow (aty, aty)))

let trans_ty aty = TArrow (edge_ty, TArrow (aty, aty))

(* Region-like levels for efficient implementation of type generalization *)
let current_level = ref 1

let enter_level () = incr current_level

let leave_level () = decr current_level

let level () = !current_level

let level_reset () = current_level := 1

(* new type variable *)
let fresh_tyvar () = TVar (ref (Unbound (Var.fresh "a", level ())))

(* equality of type variables *)
let equal_tyvars tv1 tv2 = tv1 == tv2

(* physical equality of refs *)

let reset_tyvars () =
  (* name from OCaml's typing/typetext.ml *)
  (*  Var.reset ();  *)
  (* DPW: don't need to do this *)
  level_reset ()


let tyname () = Var.fresh "a"

exception Occurs

let occurs tvr ty =
  let rec occ tvr ty =
    match ty with
    | TVar tvr' when equal_tyvars tvr tvr' -> raise Occurs
    | TVar ({contents= Unbound (name, l')} as tv) ->
        let min_level =
          match !tvr with Unbound (_, l) -> min l l' | _ -> l'
        in
        tv := Unbound (name, min_level)
    | TVar {contents= Link ty} -> occ tvr ty
    | QVar q ->
        (* this case should not occur, I don't think *)
        if_debug ("qvar " ^ Var.to_string q ^ " appears in occ check") ;
        ()
    | TArrow (t1, t2) -> occ tvr t1 ; occ tvr t2
    | TBool | TInt _ -> ()
    | TTuple ts -> List.iter (occ tvr) ts
    | TOption t -> occ tvr t
    | TMap (_, t) -> occ tvr t
    | TAll _ -> error "impredicative polymorphism in occurs check"
  in
  try occ tvr ty with Occurs ->
    error
      (Printf.sprintf "%s occurs in %s\n"
         (tyvar_to_string !tvr)
         (ty_to_string ty))


(* Simplistic.  No path compression *)
(* Also, QVar are unexpected: they should've been instantiated *)
let rec unify t1 t2 =
  if t1 == t2 then () (* t1 and t2 are physically the same *)
  else
    match (t1, t2) with
    | TVar ({contents= Unbound _} as tv), t'
     |t', TVar ({contents= Unbound _} as tv) ->
        occurs tv t' ;
        tv := Link t'
    | TVar {contents= Link t1}, t2 | t1, TVar {contents= Link t2} ->
        unify t1 t2
    | TArrow (tyl1, tyl2), TArrow (tyr1, tyr2) ->
        unify tyl1 tyr1 ; unify tyl2 tyr2
    | TBool, TBool -> ()
    | TInt i, TInt j when i = j -> ()
    | TTuple ts1, TTuple ts2 -> unifies ts1 ts2
    | TOption t1, TOption t2 -> unify t1 t2
    | TMap (i1, t1), TMap (i2, t2) when i1 = i2 -> unify t1 t2
    | TAll _, _ -> error "impredicative polymorphism in unification (1)"
    | _, TAll _ -> error "impredicative polymorphism in unification (2)"
    | _, _ ->
        error
          (Printf.sprintf "unification error: %s %s" (ty_to_string t1)
             (ty_to_string t2))


and unifies ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> ()
  | t1 :: ts1, t2 :: ts2 -> unify t1 t2 ; unifies ts1 ts2
  | _, _ -> error "wrong number of components in unification"


let unify_opt topt1 t2 = match topt1 with Some t1 -> unify t1 t2 | None -> ()

let generalize ty =
  let rec gen ty =
    match ty with
    | TVar {contents= Unbound (name, l)} when l > !current_level ->
        (Env.bind name (), QVar name)
    | TVar {contents= Link ty} -> gen ty
    | TVar _ | TBool | TInt _ -> (Env.empty, ty)
    | QVar q ->
        if_debug
          ("qvar " ^ Var.to_string q ^ " appears in generalization check") ;
        (Env.empty, ty)
    | TArrow (ty1, ty2) ->
        let tvs1, ty1 = gen ty1 in
        let tvs2, ty2 = gen ty2 in
        (Env.updates tvs1 tvs2, TArrow (ty1, ty2))
    | TTuple ts ->
        let tvs, tys = gens ts in
        (tvs, TTuple tys)
    | TOption t ->
        let tvs, ty = gen t in
        (tvs, TOption ty)
    | TMap (i, t) ->
        let tvs, ty = gen t in
        (tvs, TMap (i, ty))
    | TAll _ -> error "impredicative polymorphism in generalization"
  and gens tys =
    match tys with
    | [] -> (Env.empty, [])
    | ty1 :: tys ->
        let tvs1, ty1 = gen ty1 in
        let tvs, tys = gens tys in
        (Env.updates tvs tvs1, ty1 :: tys)
  in
  let env, ty = gen ty in
  (List.map (fun (x, _) -> x) (Env.to_list env), ty)


(* instantiation: replace schematic variables with fresh TVar *)
let inst subst ty =
  let rec loop subst ty =
    match ty with
    | QVar name -> (
      try Env.lookup subst name with Env.Unbound_var x ->
        failwith ("bad instantiation: " ^ Var.to_string x) )
    | TVar {contents= Link ty} -> loop subst ty
    | TVar {contents= Unbound (name, _)} -> (
        if_debug ("found unbound tyvar " ^ Var.to_string name) ;
        try Env.lookup subst name with Env.Unbound_var x ->
          failwith ("bad instantiation: " ^ Var.to_string x) )
    | TBool | TInt _ -> ty
    | TArrow (ty1, ty2) ->
        let ty1 = loop subst ty1 in
        let ty2 = loop subst ty2 in
        TArrow (ty1, ty2)
    | TTuple ts ->
        let ts = loops subst ts in
        TTuple ts
    | TOption t ->
        let t = loop subst t in
        TOption t
    | TMap (i, t) ->
        let t = loop subst t in
        TMap (i, t)
    | TAll _ -> error "impredicative polymorphism in instantiation"
  and loops subst tys =
    match tys with
    | [] -> []
    | ty :: tys ->
        let ty = loop subst ty in
        let tys = loops subst tys in
        ty :: tys
  in
  loop subst ty


(* instantiate schema, returning both the new type and the list of type variables *)
let inst_schema (names, ty) =
  let add_name env name =
    let tv = fresh_tyvar () in
    Env.update env name tv
  in
  let subst = List.fold_left add_name Env.empty names in
  let tys = List.map (fun name -> Env.lookup subst name) names in
  (inst subst ty, tys)


let op_typ op =
  match op with
  | And -> ([], [TBool; TBool], TBool)
  | Or -> ([], [TBool; TBool], TBool)
  | Not -> ([], [TBool], TBool)
  (* Unsigned Integer 32 operators *)
  | UAdd -> ([], [tint; tint], tint)
  | USub -> ([], [tint; tint], tint)
  | UEq -> ([], [tint; tint], TBool)
  | ULess -> ([], [tint; tint], TBool)
  | ULeq -> ([], [tint; tint], TBool)
  (* Map operations *)
  | MCreate _ -> failwith "special type for create"
  | MGet -> failwith "special type for get"
  | MSet -> failwith "special type for set"
  | MMap -> failwith "special type for map"
  | MMerge -> failwith "special type for merge"


let check_empty l s = match l with _ :: _ -> failwith s | [] -> ()

let texp (e, t) = {e; ety= Some t; espan= Span.default}

let textract e =
  match e.ety with None -> failwith "impossible" | Some ty -> (e, ty)


let rec infer_exp env (e: exp) : exp =
  match e.e with
  | EVar x -> (
    match Env.lookup_opt env x with
    | None -> error ("unbound variable " ^ Var.to_string x)
    | Some TAll (tvs, t) ->
        let ty, tys = inst_schema (tvs, t) in
        texp (ETyApp (e, tys), ty)
    | Some t -> texp (e.e, t) )
  | EVal v ->
      let v, t = infer_value env v |> textractv in
      texp (EVal v, t)
  | EOp (o, es) -> (
    match o with
    | MCreate _ | MGet | MSet | MMap | MMerge ->
        failwith "unimplemented map ops"
    | _ ->
        let tvs, argtys, resty = op_typ o in
        check_empty tvs "polymorphic operators not supported yet" ;
        let es, tys = infer_exps env es in
        unifies argtys tys ;
        texp (EOp (o, es), resty) )
  | EFun {arg= x; argty; resty; body} ->
      let ty_x = fresh_tyvar () in
      let e, ty_e = infer_exp (Env.update env x ty_x) body |> textract in
      unify_opt argty ty_x ;
      unify_opt resty ty_e ;
      texp
        ( EFun {arg= x; argty= Some ty_x; resty= Some ty_e; body}
        , TArrow (ty_x, ty_e) )
  | ETyFun (names, body) ->
      let body, ty = infer_exp env body |> textract in
      texp (ETyFun (names, body), TAll (names, ty))
  | EApp (e1, e2) ->
      let e1, ty_fun = infer_exp env e1 |> textract in
      let e2, ty_arg = infer_exp env e2 |> textract in
      let ty_res = fresh_tyvar () in
      unify ty_fun (TArrow (ty_arg, ty_res)) ;
      texp (EApp (e1, e2), ty_res)
  | ETyApp (e, tys) ->
      failwith "explicit type application unimplemented in type inference"
  | EIf (e1, e2, e3) ->
      let e1, tcond = infer_exp env e1 |> textract in
      let e2, ty2 = infer_exp env e2 |> textract in
      let e3, ty3 = infer_exp env e3 |> textract in
      unify TBool tcond ;
      unify ty2 ty3 ;
      texp (EIf (e1, e2, e3), ty2)
  | ELet (x, e1, e2) -> (
      (* TO DO? Could traverse the term e1 again replacing TVars with QVars of the same name.
           Did not do this for now. *)
      enter_level () ;
      let e1, ty_e1 = infer_exp env e1 |> textract in
      leave_level () ;
      match generalize ty_e1 with
      | [], ty ->
          let e2, ty_e2 = infer_exp (Env.update env x ty) e2 |> textract in
          texp (ELet (x, e1, e2), ty_e2)
      | tvs, ty ->
          let e2, ty_e2 =
            infer_exp (Env.update env x (TAll (tvs, ty))) e2 |> textract
          in
          texp (ELet (x, ETyFun (tvs, e1) |> exp, e2), ty_e2)
      (* NOTE:  Changes order of evaluation if e is not a value;
						        If we have effects, value restriction needed. *)
      )
  | ETuple es ->
      let es, tys = infer_exps env es in
      texp (ETuple es, TTuple tys)
  | EProj (i, e) ->
      let e, t = infer_exp env e |> textract in
      texp (EProj (i, e), t)
  | ESome e ->
      let e, t = infer_exp env e |> textract in
      texp (ESome e, TOption t)
  | EMatch (e, branches) ->
      let e, tmatch = infer_exp env e |> textract in
      let branches, t = infer_branches env tmatch branches in
      texp (EMatch (e, branches), t)
  | ETy (e, t) ->
      let e, t1 = infer_exp env e |> textract in
      unify t t1 ;
      texp (ETy (e, t1), t1)

and infer_exps env es =
  match es with
  | [] -> ([], [])
  | e :: es ->
      let e, ty = infer_exp env e |> textract in
      let es, tys = infer_exps env es in
      (e :: es, ty :: tys)

and tvalue (v, t) = {v; vty= Some t; vspan= Span.default}

and textractv v =
  match v.vty with None -> failwith "impossible" | Some ty -> (v, ty)

and infer_value env (v: Syntax.value) : Syntax.value =
  match v.v with
  | VBool b -> tvalue (v.v, TBool)
  | VUInt32 i -> tvalue (v.v, tint)
  | VMap (m, tyopt) ->
      failwith "unimplemented"
      (* To DO *)
      (*
      let i = IMap.length m in
      let (vs, default) = IMap.bindings m in
      let (default, t) = infer_value env default in
      let (vs, ts) = infer_values env (List.map (fun (_,v) -> v) vs) in
      let tv = fresh_tyvar () in
      unify t tv;
      List.iter (fun t -> unify t tv) ts;
      let t = TMap (i, tv) in
      let m = IMap.from_bindings i (vs,default) in
      (VMap (m, Some tv), t) *)
  | VTuple vs ->
      let vs, ts = infer_values env vs in
      tvalue (VTuple vs, TTuple ts)
  | VOption (None, topt) ->
      let tv = fresh_tyvar () in
      unify_opt topt tv ;
      tvalue (VOption (None, Some tv), TOption tv)
  | VOption (Some v, topt) ->
      let v, t = infer_value env v |> textractv in
      let tv = fresh_tyvar () in
      unify_opt topt tv ;
      unify t tv ;
      tvalue (VOption (Some v, Some tv), TOption tv)
  | VClosure cl ->
      failwith "unimplemented: closure type inference because i am lazy"
  | _ -> failwith "impossible"

and infer_values env vs =
  match vs with
  | [] -> ([], [])
  | v :: vs ->
      let v, t = infer_value env v |> textractv in
      let vs, ts = infer_values env vs in
      (v :: vs, t :: ts)

and infer_branches env tmatch bs =
  match bs with
  | [] -> failwith "empty branches in infer branches"
  | [(p, e)] ->
      let env2 = infer_pattern env tmatch p in
      let e, t = infer_exp env2 e |> textract in
      ([(p, e)], t)
  | (p, e) :: bs ->
      let bs, tbranch = infer_branches env tmatch bs in
      let env2 = infer_pattern env tmatch p in
      let e, t = infer_exp env2 e |> textract in
      unify t tbranch ; ((p, e) :: bs, t)

and infer_pattern env tmatch p =
  valid_pat p ;
  match p with
  | PWild -> env
  | PVar x -> Env.update env x tmatch
  | PBool _ -> unify tmatch TBool ; env
  | PUInt32 _ -> unify tmatch tint ; env
  | PTuple ps ->
      let ts = List.map (fun p -> fresh_tyvar ()) ps in
      let ty = TTuple ts in
      unify tmatch ty ; infer_patterns env ts ps
  | POption x ->
      let t = fresh_tyvar () in
      unify tmatch (TOption t) ;
      match x with None -> env | Some p -> infer_pattern env t p

and infer_patterns env ts ps =
  match (ts, ps) with
  | [], [] -> env
  | t :: ts, p :: ps ->
      valid_pat p ;
      let env = infer_pattern env t p in
      infer_patterns env ts ps
  | _, _ -> error "bad arity in pattern match"

and infer_declarations (ds: declarations) : declarations =
  match get_attr_type ds with
  | None -> error "attribute type not declared: type attribute = ..."
  | Some ty -> infer_declarations_aux Env.empty ty ds

and infer_declarations_aux env aty (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = infer_declaration env aty d in
      d' :: infer_declarations_aux env' aty ds'

and infer_declaration env aty d : ty Env.t * declaration =
  match d with
  | DLet (var, e) ->
      let e' = infer_exp env e in
      (Env.update env var (oget e'.ety), DLet (var, e'))
  | DMerge e ->
      let e' = infer_exp env e in
      let ty = oget e'.ety in
      print_endline ("merge_ty " ^ Printing.ty_to_string (merge_ty aty)) ;
      print_endline ("ty " ^ Printing.ty_to_string ty) ;
      unify ty (merge_ty aty) ;
      (Env.update env (Var.create "merge") ty, DMerge e')
  | DTrans e ->
      let e' = infer_exp env e in
      let ty = oget e'.ety in
      unify ty (trans_ty aty) ;
      (Env.update env (Var.create "trans") ty, DTrans e')
  | DInit e ->
      let e' = infer_exp env e in
      let ty = oget e'.ety in
      unify ty (init_ty aty) ;
      (Env.update env (Var.create "trans") ty, DInit e')
  | DATy _ | DNodes _ | DEdges _ -> (env, d)

(* ensure patterns do not contain duplicate variables *)
and valid_pat p = valid_pattern Env.empty p |> ignore

and valid_pattern env p =
  match p with
  | PWild -> env
  | PVar x -> (
    match Env.lookup_opt env x with
    | None -> Env.update env x ()
    | Some _ ->
        error ("variable " ^ Var.to_string x ^ " appears twice in pattern") )
  | PBool _ | PUInt32 _ -> env
  | PTuple ps -> valid_patterns env ps
  | POption None -> env
  | POption Some p -> valid_pattern env p

and valid_patterns env p =
  match p with [] -> env | p :: ps -> valid_patterns (valid_pattern env p) ps
