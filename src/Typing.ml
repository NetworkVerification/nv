(* Type inference with efficient generalization via levels; 
 * code following http://okmij.org/ftp/ML/generalization.html#levels 
 *)

open Syntax
open Printing
open Unsigned

let debug = true

let if_debug s = if debug then print_endline s else ()

let val_to_exp (v: value) : exp = {e= EVal v; ety= v.vty; espan= v.vspan}

let node_ty = tint

let edge_ty = TTuple [node_ty; node_ty]

let init_ty aty = TArrow (node_ty, aty)

let merge_ty aty = TArrow (node_ty, TArrow (aty, TArrow (aty, aty)))

let trans_ty aty = TArrow (edge_ty, TArrow (aty, aty))

let assert_ty aty = TArrow (node_ty, TArrow (aty, TBool))

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

let rec check_annot_val (v: value) =
  ( match v.vty with
  | None ->
      Console.error
        (Printf.sprintf "internal type annotation missing: %s\n"
           (Printing.value_to_string v))
  | Some _ -> () ) ;
  match v.v with
  | VOption (Some v) -> check_annot_val v
  | VTuple vs -> List.iter check_annot_val vs
  | VMap map ->
      let bs, _ = BddMap.bindings map in
      List.iter (fun (v1, v2) -> check_annot_val v1 ; check_annot_val v2) bs
  | _ -> ()

let rec check_annot (e: exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ;
  Printf.printf "type: %s\n" (Printing.ty_to_string (oget e.ety)) ; *)
  ( match e.ety with
  | None ->
      Console.error
        (Printf.sprintf "internal type annotation missing: %s\n"
           (Printing.exp_to_string e))
  | Some _ -> () ) ;
  match e.e with
  | EVar _ -> ()
  | EVal v -> check_annot_val v
  | EOp (op, es) -> List.iter check_annot es
  | EFun f -> check_annot f.body
  | EApp (e1, e2) -> check_annot e1 ; check_annot e2
  | EIf (e1, e2, e3) -> check_annot e1 ; check_annot e2 ; check_annot e3
  | ELet (_, e1, e2) -> check_annot e1 ; check_annot e2
  | ETuple es -> List.iter check_annot es
  | ESome e -> check_annot e
  | EMatch (e, bs) ->
      check_annot e ;
      List.iter (fun (_, e) -> check_annot e) bs
  | ETy (e, ty) -> check_annot e

let check_annot_decl (d: declaration) =
  match d with
  | DLet (_, _, e)
   |DSymbolic (_, Exp e)
   |DMerge e
   |DTrans e
   |DInit e
   |DAssert e
   |DRequire e ->
      check_annot e
  | DNodes _ | DEdges _ | DATy _ | DSymbolic _ -> ()

let rec check_annot_decls (ds: declarations) =
  match ds with
  | [] -> ()
  | d :: ds -> check_annot_decl d ; check_annot_decls ds

exception Invalid_type

let rec strip_ty ty =
  match ty with
  | TVar {contents= Link t} -> strip_ty t
  | TBool | TInt _ -> ty
  | TArrow (t1, t2) -> TArrow (strip_ty t1, strip_ty t2)
  | TTuple ts -> TTuple (List.map strip_ty ts)
  | TOption t -> TOption (strip_ty t)
  | TMap (ty1, ty2) -> TMap (strip_ty ty1, strip_ty ty2)
  | QVar _ | TVar _ -> raise Invalid_type

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
    | TMap (t1, t2) -> occ tvr t1 ; occ tvr t2
  in
  try occ tvr ty with Occurs ->
    Console.error
      (Printf.sprintf "%s occurs in %s\n" (tyvar_to_string !tvr)
         (ty_to_string ty))

(* Simplistic.  No path compression *)
(* Also, QVar are unexpected: they should've been instantiated *)
let rec unify info e t1 t2 : unit =
  (* similar to unify, but returns a bool indicating if it was successful *)
  let rec try_unifies ts1 ts2 : bool =
    match (ts1, ts2) with
    | [], [] -> true
    | t1 :: ts1, t2 :: ts2 -> try_unify t1 t2 && try_unifies ts1 ts2
    | _, _ -> Console.error "wrong number of components in unification"
  and try_unify t1 t2 : bool =
    if t1 == t2 then true (* t1 and t2 are physically the same *)
    else
      match (t1, t2) with
      | TVar ({contents= Unbound _} as tv), t'
       |t', TVar ({contents= Unbound _} as tv) ->
          occurs tv t' ;
          tv := Link t' ;
          true
      | TVar {contents= Link t1}, t2 -> try_unify t1 t2
      | t1, TVar {contents= Link t2} -> try_unify t1 t2
      | TArrow (tyl1, tyl2), TArrow (tyr1, tyr2) ->
          try_unify tyl1 tyr1 && try_unify tyl2 tyr2
      | TBool, TBool -> true
      | TInt i, TInt j when i = j -> true
      | TTuple ts1, TTuple ts2 -> try_unifies ts1 ts2
      | TOption t1, TOption t2 -> try_unify t1 t2
      | TMap (t1, t2), TMap (t3, t4) -> try_unify t1 t3 && try_unify t2 t4
      | _, _ -> false
  in
  if try_unify t1 t2 then ()
  else
    let msg =
      Printf.sprintf "unable to unify types: %s and %s" (ty_to_string t1)
        (ty_to_string t2)
    in
    Console.error_position info e.espan msg

and unifies info (e: exp) ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> ()
  | t1 :: ts1, t2 :: ts2 -> unify info e t1 t2 ; unifies info e ts1 ts2
  | _, _ -> Console.error "wrong number of components in unification"

let unify_opt info (e: exp) topt1 t2 =
  match topt1 with Some t1 -> unify info e t1 t2 | None -> ()

let generalize ty =
  let rec gen ty =
    match ty with
    | TVar {contents= Unbound (name, l)} when l > !current_level -> QVar name
    | TVar {contents= Link ty} -> gen ty
    | TVar _ | TBool | TInt _ -> ty
    | QVar q ->
        if_debug
          ("qvar " ^ Var.to_string q ^ " appears in generalization check") ;
        ty
    | TArrow (ty1, ty2) ->
        let ty1 = gen ty1 in
        let ty2 = gen ty2 in
        TArrow (ty1, ty2)
    | TTuple ts -> TTuple (List.map gen ts)
    | TOption t ->
        let ty = gen t in
        TOption ty
    | TMap (ty1, ty2) ->
        let ty1 = gen ty1 in
        let ty2 = gen ty2 in
        TMap (ty1, ty2)
  in
  match ty with TArrow _ -> gen ty | _ -> ty

(* instantiation: replace schematic variables with fresh TVar *)
let inst subst ty =
  let rec loop subst ty =
    match ty with
    | QVar name -> (
      try Env.lookup subst name with Env.Unbound_var x ->
        Console.error ("bad instantiation: " ^ Var.to_string x) )
    | TVar {contents= Link ty} -> loop subst ty
    | TVar {contents= Unbound (name, _)} -> (
        if_debug ("found unbound tyvar " ^ Var.to_string name) ;
        try Env.lookup subst name with Env.Unbound_var x ->
          Console.error ("bad instantiation: " ^ Var.to_string x) )
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
    | TMap (ty1, ty2) ->
        let ty1 = loop subst ty1 in
        let ty2 = loop subst ty2 in
        TMap (ty1, ty2)
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

let substitute (ty: ty) : ty =
  let map = ref Env.empty in
  let rec substitute_aux ty =
    match ty with
    | QVar name -> (
      match Env.lookup_opt !map name with
      | None ->
          let ty = fresh_tyvar () in
          map := Env.update !map name ty ;
          ty
      | Some ty -> ty )
    | TVar _ | TBool | TInt _ -> ty
    | TArrow (ty1, ty2) -> TArrow (substitute_aux ty1, substitute_aux ty2)
    | TTuple ts -> TTuple (List.map substitute_aux ts)
    | TOption t -> TOption (substitute_aux t)
    | TMap (ty1, ty2) -> TMap (substitute_aux ty1, substitute_aux ty2)
  in
  substitute_aux ty

let op_typ op =
  match op with
  | And -> ([TBool; TBool], TBool)
  | Or -> ([TBool; TBool], TBool)
  | Not -> ([TBool], TBool)
  (* Unsigned Integer 32 operators *)
  | UAdd -> ([tint; tint], tint)
  | USub -> ([tint; tint], tint)
  | ULess -> ([tint; tint], TBool)
  | ULeq -> ([tint; tint], TBool)
  (* Map operations *)
  | MCreate | MGet | MSet | MMap | MMerge | MFilter | UEq ->
      Console.error "internal error (op_typ)"

let texp (e, t) = {e; ety= Some t; espan= Span.default}

let textract e =
  match e.ety with
  | None -> Console.error "internal error (textract)"
  | Some ty -> (e, ty)

let rec infer_exp i info env (e: exp) : exp =
  (* Printf.printf "infer_exp: %s\n" (Printing.exp_to_string e) ; *)
  let exp =
    match e.e with
    | EVar x -> (
      match Env.lookup_opt env x with
      | None ->
          Console.error_position info e.espan
            ("unbound variable " ^ Var.to_string x)
      | Some t -> texp (e.e, substitute t) )
    | EVal v ->
        let v, t = infer_value info env v |> textractv in
        texp (EVal v, t)
    | EOp (o, es) -> (
      match (o, es) with
      | MGet, [e1; e2] ->
          let e1, mapty = infer_exp (i + 1) info env e1 |> textract in
          let e2, keyty = infer_exp (i + 1) info env e2 |> textract in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          texp (EOp (o, [e1; e2]), valty)
      | MSet, [e1; e2; e3] ->
          let e1, mapty = infer_exp (i + 1) info env e1 |> textract in
          let e2, keyty = infer_exp (i + 1) info env e2 |> textract in
          let e3, valty = infer_exp (i + 1) info env e3 |> textract in
          let ty = TMap (keyty, valty) in
          unify info e mapty ty ;
          texp (EOp (o, [e1; e2; e3]), ty)
      | MCreate, [e1] ->
          let e1, valty = infer_exp (i + 1) info env e1 |> textract in
          let keyty = fresh_tyvar () in
          texp (EOp (o, [e1]), TMap (keyty, valty))
      | MMap, [e1; e2] ->
          let e1, fty = infer_exp (i + 1) info env e1 |> textract in
          let e2, mapty = infer_exp (i + 1) info env e2 |> textract in
          let keyty = fresh_tyvar () in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          unify info e fty (TArrow (valty, valty)) ;
          texp (EOp (o, [e1; e2]), mapty)
      | MFilter, [e1; e2] ->
          let e1, fty = infer_exp (i + 1) info env e1 |> textract in
          let e2, mapty = infer_exp (i + 1) info env e2 |> textract in
          let keyty = fresh_tyvar () in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          unify info e fty (TArrow (keyty, TBool)) ;
          texp (EOp (o, [e1; e2]), mapty)
      | MMerge, [e1; e2; e3] ->
          let e1, fty = infer_exp (i + 1) info env e1 |> textract in
          let e2, mapty1 = infer_exp (i + 1) info env e2 |> textract in
          let e3, mapty2 = infer_exp (i + 1) info env e3 |> textract in
          let keyty = fresh_tyvar () in
          let valty = fresh_tyvar () in
          unify info e mapty1 (TMap (keyty, valty)) ;
          unify info e mapty2 (TMap (keyty, valty)) ;
          unify info e fty (TArrow (valty, TArrow (valty, valty))) ;
          texp (EOp (o, [e1; e2; e3]), mapty1)
      | MGet, _ | MSet, _ | MCreate, _ | MMap, _ | MFilter, _ | MMerge, _ ->
          Console.error_position info e.espan
            (Printf.sprintf "invalid number of parameters")
      | UEq, [e1; e2] ->
          let e1, ty1 = infer_exp (i + 1) info env e1 |> textract in
          let e2, ty2 = infer_exp (i + 1) info env e2 |> textract in
          unify info e ty1 ty2 ;
          texp (EOp (o, [e1; e2]), TBool)
      | _ ->
          let argtys, resty = op_typ o in
          let es, tys = infer_exps (i + 1) info env es in
          unifies info e argtys tys ;
          texp (EOp (o, es), resty) )
    | EFun {arg= x; argty; resty; body} ->
        let ty_x = fresh_tyvar () in
        let e, ty_e =
          infer_exp (i + 1) info (Env.update env x ty_x) body |> textract
        in
        unify_opt info e argty ty_x ;
        unify_opt info e resty ty_e ;
        texp
          ( EFun {arg= x; argty= Some ty_x; resty= Some ty_e; body= e}
          , TArrow (ty_x, ty_e) )
    | EApp (e1, e2) ->
        let e1, ty_fun = infer_exp (i + 1) info env e1 |> textract in
        let e2, ty_arg = infer_exp (i + 1) info env e2 |> textract in
        let ty_res = fresh_tyvar () in
        unify info e ty_fun (TArrow (ty_arg, ty_res)) ;
        texp (EApp (e1, e2), ty_res)
    | EIf (e1, e2, e3) ->
        let e1, tcond = infer_exp (i + 1) info env e1 |> textract in
        let e2, ty2 = infer_exp (i + 1) info env e2 |> textract in
        let e3, ty3 = infer_exp (i + 1) info env e3 |> textract in
        unify info e1 TBool tcond ;
        unify info e ty2 ty3 ;
        texp (EIf (e1, e2, e3), ty2)
    | ELet (x, e1, e2) ->
        (* TO DO? Could traverse the term e1 again replacing TVars with QVars of the same name.
           Did not do this for now. *)
        enter_level () ;
        let e1, ty_e1 = infer_exp (i + 1) info env e1 |> textract in
        leave_level () ;
        let ty = generalize ty_e1 in
        let e2, ty_e2 =
          infer_exp (i + 1) info (Env.update env x ty) e2 |> textract
        in
        texp (ELet (x, e1, e2), ty_e2)
        (* NOTE:  Changes order of evaluation if e is not a value;
						        If we have effects, value restriction needed. *)
    | ETuple es ->
        let es, tys = infer_exps (i + 1) info env es in
        texp (ETuple es, TTuple tys)
    | ESome e ->
        let e, t = infer_exp (i + 1) info env e |> textract in
        texp (ESome e, TOption t)
    | EMatch (e, branches) ->
        let e, tmatch = infer_exp (i + 1) info env e |> textract in
        let branches, t = infer_branches (i + 1) info env e tmatch branches in
        texp (EMatch (e, branches), t)
    | ETy (e, t) ->
        let e, t1 = infer_exp (i + 1) info env e |> textract in
        unify info e t t1 ;
        texp (ETy (e, t1), t1)
  in
  (* Printf.printf "type: %s\n"
    (Printing.ty_to_string (oget exp.ety)) ;
  check_annot exp ; *)
  exp

and infer_exps i info env es =
  match es with
  | [] -> ([], [])
  | e :: es ->
      let e, ty = infer_exp (i + 1) info env e |> textract in
      let es, tys = infer_exps (i + 1) info env es in
      (e :: es, ty :: tys)

and tvalue (v, t) = {v; vty= Some t; vspan= Span.default}

and textractv v =
  match v.vty with
  | None -> Console.error "internal error (textractv)"
  | Some ty -> (v, ty)

and infer_value info env (v: Syntax.value) : Syntax.value =
  (* Printf.printf "infer_value: %s\n" (Printing.value_to_string v) ; *)
  let ret =
    match v.v with
    | VBool b -> tvalue (v.v, TBool)
    | VUInt32 i -> tvalue (v.v, tint)
    | VMap m -> (
        let vs, default = BddMap.bindings m in
        let default, dty = infer_value info env default |> textractv in
        match vs with
        | [] ->
            let ty = fresh_tyvar () in
            let map = BddMap.create ~key_ty:ty default in
            tvalue (VMap map, TMap (ty, dty))
        | (kv, vv) :: _ ->
            let kv, kvty = infer_value info env kv |> textractv in
            let vv, vvty = infer_value info env vv |> textractv in
            unify info (val_to_exp v) vvty dty ;
            let vs =
              List.map
                (fun (kv2, vv2) ->
                  let kv2, kvty2 = infer_value info env kv2 |> textractv in
                  let vv2, vvty2 = infer_value info env vv2 |> textractv in
                  unify info (val_to_exp v) kvty kvty2 ;
                  unify info (val_to_exp v) vvty vvty2 ;
                  (kv2, vv2) )
                vs
            in
            let map = BddMap.from_bindings ~key_ty:kvty (vs, default) in
            tvalue (VMap map, TMap (kvty, vvty)) )
    | VTuple vs ->
        let vs, ts = infer_values info env vs in
        tvalue (VTuple vs, TTuple ts)
    | VOption None ->
        let tv = fresh_tyvar () in
        tvalue (VOption None, TOption tv)
    | VOption (Some v) ->
        let v, t = infer_value info env v |> textractv in
        let tv = fresh_tyvar () in
        unify info (val_to_exp v) t tv ;
        tvalue (VOption (Some v), TOption tv)
    | VClosure cl -> Console.error "internal error (infer_value)"
  in
  (* Printf.printf "Type: %s\n" (Printing.ty_to_string (oget ret.vty)) ; *)
  ret

and infer_values info env vs =
  match vs with
  | [] -> ([], [])
  | v :: vs ->
      let v, t = infer_value info env v |> textractv in
      let vs, ts = infer_values info env vs in
      (v :: vs, t :: ts)

and infer_branches i info env exp tmatch bs =
  match bs with
  | [] -> Console.error "internal error (infer branches)"
  | [(p, e)] ->
      let env2 = infer_pattern (i + 1) info env exp tmatch p in
      let e, t = infer_exp (i + 1) info env2 e |> textract in
      ([(p, e)], t)
  | (p, e) :: bs ->
      let bs, tbranch = infer_branches (i + 1) info env exp tmatch bs in
      let env2 = infer_pattern (i + 1) info env exp tmatch p in
      let e, t = infer_exp (i + 1) info env2 e |> textract in
      unify info e t tbranch ;
      ((p, e) :: bs, t)

and infer_pattern i info env e tmatch p =
  valid_pat p ;
  match p with
  | PWild -> env
  | PVar x -> Env.update env x tmatch
  | PBool _ -> unify info e tmatch TBool ; env
  | PUInt32 _ -> unify info e tmatch tint ; env
  | PTuple ps ->
      let ts = List.map (fun p -> fresh_tyvar ()) ps in
      let ty = TTuple ts in
      unify info e tmatch ty ;
      infer_patterns (i + 1) info env e ts ps
  | POption x ->
      let t = fresh_tyvar () in
      unify info e tmatch (TOption t) ;
      match x with
      | None -> env
      | Some p -> infer_pattern (i + 1) info env e t p

and infer_patterns i info env e ts ps =
  match (ts, ps) with
  | [], [] -> env
  | t :: ts, p :: ps ->
      valid_pat p ;
      let env = infer_pattern (i + 1) info env e t p in
      infer_patterns (i + 1) info env e ts ps
  | _, _ -> Console.error "bad arity in pattern match"

and infer_declarations i info (ds: declarations) : declarations =
  match get_attr_type ds with
  | None -> Console.error "attribute type not declared: type attribute = ..."
  | Some ty -> infer_declarations_aux (i + 1) info Env.empty ty ds

and infer_declarations_aux i info env aty (ds: declarations) : declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
      let env', d' = infer_declaration (i + 1) info env aty d in
      d' :: infer_declarations_aux (i + 1) info env' aty ds'

and infer_declaration i info env aty d : ty Env.t * declaration =
  match d with
  | DLet (x, _, e1) ->
      enter_level () ;
      let e1, ty_e1 = infer_exp (i + 1) info env e1 |> textract in
      leave_level () ;
      let ty = generalize ty_e1 in
      (Env.update env x ty, DLet (x, Some ty, texp (e1.e, ty)))
  | DSymbolic (x, e1) -> (
    match e1 with
    | Exp e1 ->
        enter_level () ;
        let e1, ty_e1 = infer_exp (i + 1) info env e1 |> textract in
        leave_level () ;
        let ty = generalize ty_e1 in
        (Env.update env x ty, DSymbolic (x, Exp (texp (e1.e, ty))))
    | Ty ty -> (Env.update env x ty, DSymbolic (x, e1)) )
  | DMerge e ->
      let e' = infer_exp (i + 1) info env e in
      let ty = oget e'.ety in
      unify info e ty (merge_ty aty) ;
      (Env.update env (Var.create "merge") ty, DMerge e')
  | DTrans e ->
      let e' = infer_exp (i + 1) info env e in
      let ty = oget e'.ety in
      unify info e ty (trans_ty aty) ;
      (Env.update env (Var.create "trans") ty, DTrans e')
  | DAssert e ->
      let e' = infer_exp (i + 1) info env e in
      let ty = oget e'.ety in
      unify info e ty (assert_ty aty) ;
      (Env.update env (Var.create "assert") ty, DAssert e')
  | DRequire e ->
      let e' = infer_exp (i + 1) info env e in
      let ty = oget e'.ety in
      unify info e ty TBool ; (env, DRequire e')
  | DInit e ->
      let e' = infer_exp (i + 1) info env e in
      let ty = oget e'.ety in
      unify info e ty (init_ty aty) ;
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
        Console.error
          ("variable " ^ Var.to_string x ^ " appears twice in pattern") )
  | PBool _ | PUInt32 _ -> env
  | PTuple ps -> valid_patterns env ps
  | POption None -> env
  | POption (Some p) -> valid_pattern env p

and valid_patterns env p =
  match p with [] -> env | p :: ps -> valid_patterns (valid_pattern env p) ps

let infer_declarations info (ds: declarations) : declarations =
  match get_attr_type ds with
  | None -> Console.error "attribute type not declared: type attribute = ..."
  | Some ty -> infer_declarations_aux 0 info Env.empty ty ds
