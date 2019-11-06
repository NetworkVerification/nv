(* Type inference with efficient generalization via levels;
 * code following http://okmij.org/ftp/ML/generalization.html#levels
*)

open Syntax
open Printing
open Nv_datastructures
open Nv_utils
open Collections
open Batteries

let debug = true

let if_debug s = if debug then print_endline s else ()

let node_ty = TNode

let edge_ty = TEdge

let init_ty aty = TArrow (node_ty, aty)

let merge_ty aty = TArrow (node_ty, TArrow (aty, TArrow (aty, aty)))

let trans_ty aty = TArrow (edge_ty, TArrow (aty, aty))

let assert_ty aty = TArrow (node_ty, TArrow (aty, TBool))

(* TODO: do we want a special partition ID type? is i8 a sensible number? *)
(* partitioning *)
let partition_ty = TArrow (node_ty, TInt 8)

let interface_ty aty = TArrow (edge_ty, TOption aty)
(* end partitioning *)

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

(* List of record types that are declared *)
let record_types = ref []

let rec check_annot_val (v: value) =
  ( match v.vty with
    | None ->
      Console.error
        (Printf.sprintf "internal type annotation missing: %s\n"
           (Printing.value_to_string v))
    | Some _ -> () ) ;
  match v.v with
  | VOption (Some v) -> check_annot_val v
  | VTuple vs -> BatList.iter check_annot_val vs
  | VMap map ->
    let bs, _ = BddMap.bindings map in
    BatList.iter
      (fun (v1, v2) -> check_annot_val v1 ; check_annot_val v2)
      bs
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
  | EOp (_, es) -> BatList.iter check_annot es
  | EFun f -> check_annot f.body
  | EApp (e1, e2) -> check_annot e1 ; check_annot e2
  | EIf (e1, e2, e3) ->
    check_annot e1 ; check_annot e2 ; check_annot e3
  | ELet (_, e1, e2) -> check_annot e1 ; check_annot e2
  | ETuple es -> BatList.iter check_annot es
  | ESome e -> check_annot e
  | EMatch (e, bs) ->
    check_annot e ;
    iterBranches (fun (_, e) -> check_annot e) bs
  | ETy (e, _) | EProject (e, _) -> check_annot e
  | ERecord map -> StringMap.iter (fun _ -> check_annot) map

let check_annot_decl (d: declaration) =
  match d with
  | DLet (_, _, e)
  | DSymbolic (_, Exp e)
  | DMerge e
  | DTrans e
  | DInit e
  | DAssert e
  | DPartition e (* partitioning *)
  | DInterface e (* partitioning *)
  | DRequire e ->
    check_annot e
  | DNodes _ | DEdges _ | DATy _ | DSymbolic _ | DUserTy _ -> ()

let rec check_annot_decls (ds: declarations) =
  match ds with
  | [] -> ()
  | d :: ds -> check_annot_decl d ; check_annot_decls ds

exception Invalid_type

let rec strip_ty ty =
  match ty with
  | TVar {contents= Link t} -> strip_ty t
  | TUnit | TBool | TInt _ | TNode | TEdge -> ty
  | TArrow (t1, t2) -> TArrow (strip_ty t1, strip_ty t2)
  | TTuple ts -> TTuple (BatList.map strip_ty ts)
  | TOption t -> TOption (strip_ty t)
  | TMap (ty1, ty2) -> TMap (strip_ty ty1, strip_ty ty2)
  | TRecord map -> TRecord (StringMap.map strip_ty map)
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
    | TUnit | TBool | TInt _ | TNode | TEdge -> ()
    | TRecord map -> StringMap.iter (fun _ -> occ tvr) map
    | TTuple ts -> BatList.iter (occ tvr) ts
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
    | _, _ -> false
  and try_unify t1 t2 : bool =
    if t1 == t2 then true (* t1 and t2 are physically the same *)
    else
      match (t1, t2) with
      | (TVar {contents = Link t1},t2)
      | (t1,TVar {contents = Link t2}) -> try_unify t1 t2
      | TVar ({contents= Unbound _} as tv), t'
      | t', TVar ({contents= Unbound _} as tv) ->
        occurs tv t' ;
        tv := Link t' ;
        true
      (* | TVar {contents= Link t1}, t2 -> try_unify t1 t2
       * | t1, TVar {contents= Link t2} -> try_unify t1 t2 *)
      | TArrow (tyl1, tyl2), TArrow (tyr1, tyr2) ->
        try_unify tyl1 tyr1 && try_unify tyl2 tyr2
      | TBool, TBool -> true
      | TInt i, TInt j when i = j -> true
      | TNode, TNode -> true
      | TEdge, TEdge -> true
      | TTuple ts1, TTuple ts2 -> try_unifies ts1 ts2
      | TOption t1, TOption t2 -> try_unify t1 t2
      | TMap (t1, t2), TMap (t3, t4) ->
        try_unify t1 t3 && try_unify t2 t4
      | TRecord map1, TRecord map2 ->
        let open RecordUtils in
        if not (same_labels map1 map2)
        then false
        else BatList.fold_left
            (fun b l -> b &&
                        try_unify
                          (StringMap.find l map1)
                          (StringMap.find l map2))
            true (get_record_labels map1)
      | _, _ -> false
  in
  if try_unify t1 t2 then ()
  else
    let msg =
      Printf.sprintf "unable to unify types: %s and\n %s"
        (ty_to_string t1) (ty_to_string t2)
    in
    Printf.printf "%s\n" msg;
    Console.error_position info e.espan msg

and unifies info (e: exp) ts1 ts2 =
  match (ts1, ts2) with
  | [], [] -> ()
  | t1 :: ts1, t2 :: ts2 ->
    unify info e t1 t2 ; unifies info e ts1 ts2
  | _, _ -> Console.error "wrong number of components in unification"

let unify_opt info (e: exp) topt1 t2 =
  match topt1 with Some t1 -> unify info e t1 t2 | None -> ()

let generalize ty =
  let rec gen ty =
    match ty with
    | TVar {contents= Unbound (name, l)} when l > !current_level ->
      QVar name
    | TVar {contents= Link ty} -> gen ty
    | TVar _ | TUnit | TBool | TInt _ | TNode | TEdge -> ty
    | QVar q ->
      if_debug
        ( "qvar " ^ Var.to_string q
          ^ " appears in generalization check" ) ;
      ty
    | TArrow (ty1, ty2) ->
      let ty1 = gen ty1 in
      let ty2 = gen ty2 in
      TArrow (ty1, ty2)
    | TRecord map -> TRecord (StringMap.map gen map)
    | TTuple ts -> TTuple (BatList.map gen ts)
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
          Console.error ("bad instantiation: " ^ x) )
    | TVar {contents= Link ty} -> loop subst ty
    | TVar {contents= Unbound (name, _)} -> (
        if_debug ("found unbound tyvar " ^ Var.to_string name) ;
        try Env.lookup subst name with Env.Unbound_var x ->
          Console.error ("bad instantiation: " ^ x) )
    | TUnit | TBool | TInt _ | TNode | TEdge -> ty
    | TArrow (ty1, ty2) ->
      let ty1 = loop subst ty1 in
      let ty2 = loop subst ty2 in
      TArrow (ty1, ty2)
    | TTuple ts ->
      let ts = loops subst ts in
      TTuple ts
    | TRecord map ->
      TRecord (StringMap.map (loop subst) map)
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
  let subst = BatList.fold_left add_name Env.empty names in
  let tys = BatList.map (fun name -> Env.lookup subst name) names in
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
    | TVar _ | TUnit | TBool | TInt _ | TNode | TEdge -> ty
    | TArrow (ty1, ty2) ->
      TArrow (substitute_aux ty1, substitute_aux ty2)
    | TRecord map -> TRecord (StringMap.map substitute_aux map)
    | TTuple ts -> TTuple (BatList.map substitute_aux ts)
    | TOption t -> TOption (substitute_aux t)
    | TMap (ty1, ty2) -> TMap (substitute_aux ty1, substitute_aux ty2)
  in
  substitute_aux ty

let op_typ op =
  match op with
  | And -> ([TBool; TBool], TBool)
  | Or -> ([TBool; TBool], TBool)
  | Not -> ([TBool], TBool)
  (* Integer operators *)
  | UAdd size -> ([tint_of_size size; tint_of_size size], tint_of_size size)
  | USub size -> ([tint_of_size size; tint_of_size size], tint_of_size size)
  | ULess size-> ([tint_of_size size; tint_of_size size], TBool)
  | ULeq size -> ([tint_of_size size; tint_of_size size], TBool)
  | NLess -> ([TNode; TNode], TBool)
  | NLeq -> ([TNode; TNode], TBool)
  | AtMost n ->
    ([TTuple (BatList.init n (fun _ -> TBool));
      TTuple (BatList.init n (fun _ -> TInt 32));
      (TInt 32)], TBool)
  | TGet _ | TSet _ ->
    failwith "internal error (op_typ): tuple op"
  (* Map operations *)
  | MCreate | MGet | MSet | MMap | MMerge | MMapFilter | MMapIte | MFoldNode | MFoldEdge | Eq ->
    failwith "internal error (op_typ): map op"

let texp (e, ty, span) = aexp (e, Some ty, span)

let tvalue (v, ty, span) = avalue (v, Some ty, span)

let textract e =
  match e.ety with
  | None -> failwith "internal error (textract)"
  | Some ty -> (e, ty)

let rec infer_exp i info env (e: exp) : exp =
  let exp =
    match e.e with
    | EVar x -> (
        match Env.lookup_opt env x with
        | None ->
          Console.error_position info e.espan
            (* failwith *) ("unbound variable " ^ Var.to_string x)
        | Some t -> texp (e, substitute t, e.espan) )
    | EVal v ->
      let v, t = infer_value info env v |> textractv in
      texp (e_val v, t, e.espan)
    | EOp (o, es) -> (
        match (o, es) with
        | MGet, [e1; e2] ->
          let e1, mapty =
            infer_exp (i + 1) info env e1 |> textract
          in
          let e2, keyty =
            infer_exp (i + 1) info env e2 |> textract
          in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          texp (eop o [e1; e2], valty, e.espan)
        | MSet, [e1; e2; e3] ->
          let e1, mapty =
            infer_exp (i + 1) info env e1 |> textract
          in
          let e2, keyty =
            infer_exp (i + 1) info env e2 |> textract
          in
          let e3, valty =
            infer_exp (i + 1) info env e3 |> textract
          in
          let ty = TMap (keyty, valty) in
          unify info e mapty ty ;
          texp (eop o [e1; e2; e3], ty, e.espan)
        | MCreate, [e1] ->
          let e1, valty =
            infer_exp (i + 1) info env e1 |> textract
          in
          let keyty = fresh_tyvar () in
          texp (eop o [e1], TMap (keyty, valty), e.espan)
        | MMap, [e1; e2] ->
          let e1, fty = infer_exp (i + 1) info env e1 |> textract in
          let e2, mapty =
            infer_exp (i + 1) info env e2 |> textract
          in
          let keyty = fresh_tyvar () in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          unify info e fty (TArrow (valty, valty)) ;
          texp (eop o [e1; e2], mapty, e.espan)
        | MMapFilter, [e1; e2; e3] ->
          let e1, kty = infer_exp (i + 1) info env e1 |> textract in
          let e2, vty = infer_exp (i + 1) info env e2 |> textract in
          let e3, mapty =
            infer_exp (i + 1) info env e3 |> textract
          in
          let keyty = fresh_tyvar () in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          unify info e kty (TArrow (keyty, TBool)) ;
          unify info e vty (TArrow (valty, valty)) ;
          texp (eop o [e1; e2; e3], mapty, e.espan)
        | MMapIte, [e1; e2; e3; e4] ->
          let e1, kty = infer_exp (i + 1) info env e1 |> textract in
          let e2, vty1 = infer_exp (i + 1) info env e2 |> textract in
          let e3, vty2 =
            infer_exp (i + 1) info env e3 |> textract
          in
          let e4, mapty =
            infer_exp (i + 1) info env e4 |> textract
          in
          let keyty = fresh_tyvar () in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          unify info e kty (TArrow (keyty, TBool)) ;
          unify info e vty1 (TArrow (valty, valty)) ;
          unify info e vty2 (TArrow (valty, valty)) ;
          texp (eop o [e1; e2; e3; e4], mapty, e.espan)
        | MMerge, _ ->
          let (e1, e2, e3), rest =
            match es with
            | [e1; e2; e3] -> ((e1, e2, e3), None)
            | [e1; e2; e3; el0; el1; er0; er1] ->
              ((e1, e2, e3), Some (el0, el1, er0, er1))
            | _ ->
              Console.error_position info e.espan
                (Printf.sprintf "invalid number of parameters")
          in
          let e1, fty = infer_exp (i + 1) info env e1 |> textract in
          let e2, mapty1 =
            infer_exp (i + 1) info env e2 |> textract
          in
          let e3, mapty2 =
            infer_exp (i + 1) info env e3 |> textract
          in
          let keyty = fresh_tyvar () in
          let valty = fresh_tyvar () in
          unify info e mapty1 (TMap (keyty, valty)) ;
          unify info e mapty2 (TMap (keyty, valty)) ;
          unify info e fty (TArrow (valty, TArrow (valty, valty))) ;
          let es =
            match rest with
            | None -> []
            | Some (el0, el1, er0, er1) ->
              let el0, tyl0 =
                infer_exp (i + 1) info env el0 |> textract
              in
              let el1, tyl1 =
                infer_exp (i + 1) info env el1 |> textract
              in
              let er0, tyr0 =
                infer_exp (i + 1) info env er0 |> textract
              in
              let er1, tyr1 =
                infer_exp (i + 1) info env er1 |> textract
              in
              unify info e tyl0 (TOption valty) ;
              unify info e tyl1 (TOption valty) ;
              unify info e tyr0 (TOption valty) ;
              unify info e tyr1 (TOption valty) ;
              [el0; el1; er0; er1]
          in
          texp (eop o (e1 :: e2 :: e3 :: es), mapty1, e.espan)
        | MFoldNode, [e1; e2; e3] ->
          let e1, fty = infer_exp (i + 1) info env e1 |> textract in
          let e2, mapty =
            infer_exp (i + 1) info env e2 |> textract
          in
          let e3, accty =
            infer_exp (i + 1) info env e3 |> textract
          in
          let keyty = TNode in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          unify info e fty (TArrow (keyty, TArrow(valty, TArrow(accty, accty)))) ;
          texp (eop o [e1; e2; e3], accty, e.espan)
        | MFoldEdge, [e1; e2; e3] ->
          let e1, fty = infer_exp (i + 1) info env e1 |> textract in
          let e2, mapty =
            infer_exp (i + 1) info env e2 |> textract
          in
          let e3, accty =
            infer_exp (i + 1) info env e3 |> textract
          in
          let keyty = TEdge in
          let valty = fresh_tyvar () in
          unify info e mapty (TMap (keyty, valty)) ;
          unify info e fty (TArrow (keyty, TArrow(valty, TArrow(accty, accty)))) ;
          texp (eop o [e1; e2; e3], accty, e.espan)
        | TGet (size, lo, hi), [e1] ->
          let e1, tty = infer_exp (i + 1) info env e1 |> textract in
          let elt_tyvars = (List.map (fun _ -> fresh_tyvar ()) (List.make size ())) in
          unify info e tty (TTuple elt_tyvars) ;
          let ret_ty =
            if lo = hi then
              List.nth elt_tyvars lo
            else
              TTuple (List.drop lo elt_tyvars |> List.take (hi - lo + 1))
          in
          texp (eop o [e1], ret_ty, e.espan)
        | TSet (size, lo, hi), [e1; e2] ->
          let e1, tty = infer_exp (i + 1) info env e1 |> textract in
          let e2, vty = infer_exp (i + 1) info env e2 |> textract in
          let elt_tyvars = (List.map (fun _ -> fresh_tyvar ()) (List.make size ())) in
          unify info e tty (TTuple elt_tyvars) ;
          (if lo = hi then
             unify info e vty (List.nth elt_tyvars lo)
           else
             unify info e vty (TTuple (List.drop lo elt_tyvars |> List.take (hi - lo + 1)))
          );
          texp (eop o [e1;e2], tty, e.espan)
        | MGet, _ | MSet, _ | MCreate, _ | MMap, _ | MFoldNode, _ | MFoldEdge, _
        | TGet _, _ | TSet _, _ ->
          Console.error_position info e.espan
            (Printf.sprintf "invalid number of parameters")
        | Eq, [e1; e2] ->
          let e1, ty1 = infer_exp (i + 1) info env e1 |> textract in
          let e2, ty2 = infer_exp (i + 1) info env e2 |> textract in
          unify info e ty1 ty2 ;
          texp (eop o [e1; e2], TBool, e.espan)
        | _ ->
          let argtys, resty = op_typ o in
          let es, tys = infer_exps (i + 1) info env es in
          unifies info e argtys tys ;
          texp (eop o es, resty, e.espan) )
    | EFun {arg= x; argty; resty; body} ->
      let ty_x = fresh_tyvar () in
      let e, ty_e =
        infer_exp (i + 1) info (Env.update env x ty_x) body
        |> textract
      in
      unify_opt info e argty ty_x ;
      unify_opt info e resty ty_e ;
      texp
        ( efun {arg= x; argty= Some ty_x; resty= Some ty_e; body= e}
        , TArrow (ty_x, ty_e)
        , e.espan )
    | EApp (e1, e2) ->
      let e1, ty_fun = infer_exp (i + 1) info env e1 |> textract in
      let e2, ty_arg = infer_exp (i + 1) info env e2 |> textract in
      let ty_res = fresh_tyvar () in
      unify info e ty_fun (TArrow (ty_arg, ty_res)) ;
      texp (eapp e1 e2, ty_res, e.espan)
    | EIf (e1, e2, e3) ->
      let e1, tcond = infer_exp (i + 1) info env e1 |> textract in
      let e2, ty2 = infer_exp (i + 1) info env e2 |> textract in
      let e3, ty3 = infer_exp (i + 1) info env e3 |> textract in
      unify info e1 TBool tcond ;
      unify info e ty2 ty3 ;
      texp (eif e1 e2 e3, ty2, e.espan)
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
      texp (elet x e1 e2, ty_e2, e.espan)
    (* NOTE:  Changes order of evaluation if e is not a value;
       If we have effects, value restriction needed. *)
    | ETuple es ->
      let es, tys = infer_exps (i + 1) info env es in
      texp (etuple es, TTuple tys, e.espan)
    | ERecord emap ->
      (* Retrieve the record type corresponding to this expression.
         All record types should be explicitly declared, and
         all labels should appear in exactly one declaration *)
      let open RecordUtils in
      let label = (List.hd @@ get_record_labels emap) in
      let ferr = (Console.error_position info e.espan) in
      let tmap = get_type_with_label (!record_types) ferr label in

      (if not (same_labels emap tmap) then
         (* The only possible record type was not a match *)
         Console.error_position info e.espan
           "Record does not match any declared record type!");

      let emap = StringMap.map (infer_exp (i+1) info env) emap in

      BatEnum.iter
        (fun l ->
           let e, t1 = StringMap.find l emap |> textract in
           let t2 = StringMap.find l tmap in
           unify info e t1 t2)
        (StringMap.keys emap);

      texp (erecord emap, TRecord tmap, e.espan)
    | EProject (e1, label) ->
      (* Retrieve the record type containing this label.
         All record types should be explicitly declared, and
         all labels should appear in exactly one declaration *)
      let open RecordUtils in
      let ferr = (Console.error_position info e.espan) in
      let tmap = get_type_with_label (!record_types) ferr label in

      let label_type = StringMap.find label tmap in
      let e1, ety = infer_exp (i + 1) info env e1 |> textract in
      unify info e1 ety (TRecord tmap) ;

      texp (eproject e1 label, label_type, e.espan)
    | ESome e ->
      let e, t = infer_exp (i + 1) info env e |> textract in
      texp (esome e, TOption t, e.espan)
    | EMatch (e1, branches) ->
      let e1, tmatch = infer_exp (i + 1) info env e1 |> textract in
      let branches, t =
        infer_branches (i + 1) info env e1 tmatch branches
      in
      texp (ematch e1 branches, t, e1.espan)
    | ETy (e, t) ->
      let e, t1 = infer_exp (i + 1) info env e |> textract in
      unify info e t t1 ;
      texp (ety e t1, t1, e.espan)
  in
  (* Printf.printf "infer_exp: %s\n" (Printing.exp_to_string e) ;
     Printf.printf "type: %s\n" (Printing.ty_to_string (oget exp.ety)) ;
     check_annot exp ; *)
  exp

and infer_exps i info env es =
  match es with
  | [] -> ([], [])
  | e :: es ->
    let e, ty = infer_exp (i + 1) info env e |> textract in
    let es, tys = infer_exps (i + 1) info env es in
    (e :: es, ty :: tys)

and textractv v =
  match v.vty with
  | None -> failwith "internal error (textractv)"
  | Some ty -> (v, ty)

and infer_value info env (v: Syntax.value) : Syntax.value =
  (* Printf.printf "infer_value: %s\n" (Printing.value_to_string v) ; *)
  let ret =
    match v.v with
    | VUnit -> tvalue (v, TUnit, v.vspan)
    | VBool _ -> tvalue (v, TBool, v.vspan)
    | VInt i -> tvalue (v, tint_of_value i, v.vspan)
    | VNode _ -> tvalue (v, TNode, v.vspan)
    | VEdge _ -> tvalue (v, TEdge, v.vspan)
    | VMap m -> (
        let vs, default = BddMap.bindings m in
        let default, dty =
          infer_value info env default |> textractv
        in
        match vs with
        | [] ->
          (* let ty = fresh_tyvar () in *)
          let ty = fresh_tyvar () in
          tvalue (vmap m, TMap (ty, dty), v.vspan)
        (* (match v.vty with *)
        (*  | None -> *)
        (*     let ty = fresh_tyvar () in *)
        (*     tvalue (vmap m, TMap (ty, dty), v.vspan) *)
        (*  | Some ty -> *)
        (*     let map = BddMap.create ~key_ty:ty default in *)
        (*     tvalue (vmap map, TMap (ty, dty), v.vspan)) *)
        | (kv, vv) :: _ ->
          let _, kvty = infer_value info env kv |> textractv in
          let _, vvty = infer_value info env vv |> textractv in
          unify info (exp_of_value v) vvty dty ;
          let vs =
            BatList.map
              (fun (kv2, vv2) ->
                 let kv2, kvty2 =
                   infer_value info env kv2 |> textractv
                 in
                 let vv2, vvty2 =
                   infer_value info env vv2 |> textractv
                 in
                 unify info (exp_of_value v) kvty kvty2 ;
                 unify info (exp_of_value v) vvty vvty2 ;
                 (kv2, vv2) )
              vs
          in
          let map =
            BddMap.from_bindings ~key_ty:kvty (vs, default)
          in
          tvalue (vmap map, TMap (kvty, vvty), v.vspan) )
    | VTuple vs ->
      let vs, ts = infer_values info env vs in
      tvalue (vtuple vs, TTuple ts, v.vspan)
    | VRecord vmap ->
      (* All VRecords are constructed via ERecords, so shouldn't need
         to check that the record type has been properly declared *)
      let vmap = StringMap.map (infer_value info env) vmap in
      let tmap = StringMap.map (fun v -> Nv_utils.OCamlUtils.oget v.vty) vmap in
      tvalue (vrecord vmap, TRecord tmap, v.vspan)
    | VOption None ->
      let tv = fresh_tyvar () in
      tvalue (voption None, TOption tv, v.vspan)
    | VOption (Some v) ->
      let v, t = infer_value info env v |> textractv in
      let tv = fresh_tyvar () in
      unify info (exp_of_value v) t tv ;
      tvalue (voption (Some v), TOption tv, v.vspan)
    | VClosure _ -> failwith "internal error (infer_value)"
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
  match popBranch bs with
  | ((p, e), bs) when isEmptyBranch bs ->
    let env2 = infer_pattern (i + 1) info env exp tmatch p in
    let e, t = infer_exp (i + 1) info env2 e |> textract in
    (addBranch p e emptyBranch, t)
  | ((p, e), bs) ->
    let bs, tbranch =
      infer_branches (i + 1) info env exp tmatch bs
    in
    let env2 = infer_pattern (i + 1) info env exp tmatch p in
    let e, t = infer_exp (i + 1) info env2 e |> textract in
    unify info e t tbranch ;
    (addBranch p e bs, t)

(* and infer_branches i info env exp tmatch bs = *)
(*   let rec infer_branches_aux i info env exp tmatch bs accbs accty = *)
(*     try let ((p,e), bs) = popBranch bs in *)
(*         let env2 = infer_pattern (i + 1) info env exp tmatch p in *)
(*         let e, t = infer_exp (i + 1) info env2 e |> textract in *)
(*         unify info e t accty ; *)
(*         infer_branches_aux (i+1) info env exp tmatch bs (addBranch p e accbs) t *)
(*     with *)
(*     | Not_found -> (accbs, accty) *)
(*   in *)
(*   try let ((p, e), bs) = popBranch bs in *)
(*       let env2 = infer_pattern (i + 1) info env exp tmatch p in *)
(*       let e, t = infer_exp (i + 1) info env2 e |> textract in *)
(*       infer_branches_aux (i+1) info env exp tmatch bs (addBranch p e emptyBranch) t *)
(*   with | Not_found -> failwith "internal error (infer branches)" *)

and infer_pattern i info env e tmatch p =
  valid_pat p ;
  match p with
  | PWild -> env
  | PVar x -> Env.update env x tmatch
  | PUnit ->
    unify info e tmatch TUnit ;
    env
  | PBool _ ->
    unify info e tmatch TBool ;
    env
  | PInt i ->
    unify info e tmatch (tint_of_value i);
    env
  | PNode _ ->
    unify info e tmatch TNode ;
    env
  | PEdge (p1, p2) ->
    unify info e tmatch TEdge ;
    infer_patterns (i + 1) info env e [TNode; TNode] [p1; p2]
  | PTuple ps ->
    let ts = BatList.map (fun _ -> fresh_tyvar ()) ps in
    let ty = TTuple ts in
    unify info e tmatch ty ;
    infer_patterns (i + 1) info env e ts ps
  | PRecord pmap ->
    let ptmap = StringMap.map (fun p -> p, fresh_tyvar ()) pmap in
    let tmap = StringMap.map snd ptmap in
    let ty = TRecord (tmap) in
    unify info e tmatch ty ;
    StringMap.fold
      (fun _ (p, t) env ->
         infer_pattern (i + 1) info env e t p)
      ptmap env
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
  | None ->
    Console.error
      "attribute type not declared: type attribute = ..."
  | Some ty -> infer_declarations_aux (i + 1) info Env.empty ty ds

and infer_declarations_aux i info env aty (ds: declarations) :
  declarations =
  match ds with
  | [] -> []
  | d :: ds' ->
    let env', d' = infer_declaration (i + 1) info env aty d in
    d' :: infer_declarations_aux (i + 1) info env' aty ds'

and infer_declaration i info env aty d : ty Env.t * declaration =
  let open Nv_utils.OCamlUtils in
  match d with
  | DLet (x, _, e1) ->
    enter_level () ;
    let e1, ty_e1 = infer_exp (i + 1) info env e1 |> textract in
    leave_level () ;
    let ty = generalize ty_e1 in
    ( Env.update env x ty
    , DLet (x, Some ty, texp (e1, ty, e1.espan)) )
  | DSymbolic (x, e1) -> (
      match e1 with
      | Exp e1 ->
        enter_level () ;
        let e1, ty_e1 = infer_exp (i + 1) info env e1 |> textract in
        leave_level () ;
        let ty = generalize ty_e1 in
        ( Env.update env x ty
        , DSymbolic (x, Exp (texp (e1, ty, e1.espan))) )
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
  (* partitioning *)
  | DPartition e ->
    let e' = infer_exp (i + 1) info env e in
    let ty = oget e'.ety in
    unify info e ty partition_ty ;
    (Env.update env (Var.create "partition") ty, DPartition e')
  | DInterface e ->
    let e' = infer_exp (i + 1) info env e in
    let ty = oget e'.ety in
    unify info e ty (interface_ty aty) ;
    (Env.update env (Var.create "interface") ty, DInterface e')
  (* end partitioning *)
  | DRequire e ->
    let e' = infer_exp (i + 1) info env e in
    let ty = oget e'.ety in
    unify info e ty TBool ; (env, DRequire e')
  | DInit e ->
    let e' = infer_exp (i + 1) info env e in
    let ty = oget e'.ety in
    unify info e ty (init_ty aty) ;
    (Env.update env (Var.create "init") ty, DInit e')
  | DATy _ | DUserTy _ | DNodes _ | DEdges _ -> (env, d)

(* ensure patterns do not contain duplicate variables *)
and valid_pat p = valid_pattern Env.empty p |> ignore

and valid_pattern env p =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PNode _ -> env
  | PVar x -> (
      match Env.lookup_opt env x with
      | None -> Env.update env x ()
      | Some _ ->
        Console.error
          ( "variable " ^ Var.to_string x
            ^ " appears twice in pattern" ) )
  | PEdge (p1, p2) -> valid_patterns env [p1; p2]
  | PTuple ps -> valid_patterns env ps
  | PRecord map ->
    StringMap.fold (fun _ p env -> valid_pattern env p) map env
  | POption None -> env
  | POption (Some p) -> valid_pattern env p

and valid_patterns env p =
  match p with
  | [] -> env
  | p :: ps -> valid_patterns (valid_pattern env p) ps

let canonicalize_type (ty : ty) : ty =
  let rec aux ty map count =
    match ty with
    | TUnit
    | TBool
    | TInt _
    | TNode
    | TEdge ->
      ty, map, count
    | TArrow (t1, t2) ->
      let t1', map, count = aux t1 map count in
      let t2', map, count = aux t2 map count in
      TArrow (t1', t2'), map, count
    | TTuple (tys) ->
      let tys', map, count =
        BatList.fold_left
          (fun (lst, map, count) t ->
             let t', map, count = aux t map count in
             t' :: lst, map, count
          )
          ([], map, count) tys
      in
      TTuple (BatList.rev tys'), map, count
    | TRecord (tmap) ->
      let open RecordUtils in
      let tmap', map, count =
        List.fold_left2
          (fun (tmap, map, count) l t ->
             let t', map, count = aux t map count in
             StringMap.add l t' tmap, map, count
          )
          (StringMap.empty, map, count) (get_record_labels tmap) (get_record_entries tmap)
      in
      TRecord tmap', map, count
    | TOption t ->
      let t', map, count = aux t map count in
      TOption (t'), map, count
    | TMap (t1, t2) ->
      let t1', map, count = aux t1 map count in
      let t2', map, count = aux t2 map count in
      TMap (t1', t2'), map, count
    | QVar tyname ->
      begin
        match VarMap.Exceptionless.find tyname map with
        | None ->
          let new_var = Var.to_var ("a", count) in
          ( QVar (new_var),
            (VarMap.add tyname new_var map),
            count + 1)
        | Some v -> QVar (v), map, count
      end
    | TVar r ->
      begin
        match !r with
        | Link t -> aux t map count
        | Unbound _ -> TUnit, map, count
      end
  in
  let (result, _, _) = aux ty (VarMap.empty) 0 in
  result


let rec equiv_tys ty1 ty2 =
  equal_tys (canonicalize_type ty1) (canonicalize_type ty2)
;;

let infer_declarations info (ds: declarations) : declarations =
  match get_attr_type ds with
  | None ->
    Console.error
      "attribute type not declared: type attribute = ..."
  | Some ty ->
    record_types := get_record_types ds ;
    infer_declarations_aux 0 info Env.empty ty ds
