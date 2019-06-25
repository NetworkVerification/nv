open Collections
open Syntax
open Slicing

let rec flatten_ty ty =
  match ty with
  | TVar {contents= Link t} -> flatten_ty t
  | TUnit | TBool | TInt _ | TNode -> ty
  | TArrow (t1, t2) ->
    let ty1 = flatten_ty t1 in
    (match ty1 with
     | TTuple ts ->
       BatList.fold_right (fun t acc ->
           TArrow (t, acc)) ts (flatten_ty t2)
     | _ ->
       TArrow (ty1, flatten_ty t2))
  | TEdge -> flatten_ty (TTuple [TNode; TNode])
  | TTuple ts ->
    let ts = BatList.map flatten_ty ts in
    let ts' = BatList.fold_right (fun ty acc ->
        match ty with
        | TTuple ts -> BatList.append ts acc
        | _ -> ty :: acc) ts []
    in
    TTuple ts'
  | TOption ty -> TOption (flatten_ty ty)
  | TMap (ty1, ty2) ->
    TMap (flatten_ty ty1, flatten_ty ty2)
  | TRecord ty -> failwith "record's should be unrolled first"
  | QVar _ | TVar _ -> failwith "internal error (flatten_ty)"

let rec flatten_val v =
  match v.v with
  | VUnit | VBool _ | VInt _ | VNode _ | VOption None -> v
  | VOption (Some v) ->
    avalue (voption (Some (flatten_val v)), Some (flatten_ty (oget v.vty)), v.vspan)
  | VEdge (n1, n2) ->
    let v1 = avalue (vnode n1, Some TNode, v.vspan) in
    let v2 = avalue (vnode n2, Some TNode, v.vspan) in
    flatten_val @@ avalue (vtuple [v1; v2], Some (TTuple [TNode; TNode]), v.vspan)
  | VTuple vs ->
    let vs = BatList.map flatten_val vs in
    let vs' = BatList.fold_right (fun v acc ->
        match v.v with
        | VTuple vs -> BatList.append vs acc
        | _ -> v :: acc) vs []
    in
    avalue (vtuple vs', Some (flatten_ty (oget v.vty)), v.vspan)
  | VClosure _ -> failwith "Closures not yet implemented"
  | VRecord _ -> failwith "Record value found during flattening"
  | VMap _ -> failwith "Map value found during flattening"

let rec flatten_exp e : exp =
  match e.e with
  | ETy (e, ty) -> flatten_exp e
  | EVal v ->
    let v = flatten_val v in
    (* Printf.printf "%s\n" (Syntax.show_value ~show_meta:false v); *)
    aexp (e_val v, v.vty, v.vspan)
  | EVar x ->
    let ty = flatten_ty (oget e.ety) in
    (match ty with
     | TTuple ts ->
       let es =
         BatList.mapi (fun i ty ->
             aexp(evar (proj_var i x), Some ty, Span.default)) ts
       in
       aexp(etuple es, Some ty, e.espan)
     | _ ->
       aexp(e, Some ty, e.espan))
  | EFun {arg = x; argty = Some xty; resty= Some resty; body= body} ->
    let body = flatten_exp body in
    let xty = flatten_ty xty in
    (match xty with
     | TTuple ts ->
       BatList.fold_righti (fun i ty acce ->
           aexp (efun
                   { arg = proj_var i x;
                     argty = Some ty;
                     resty = acce.ety;
                     body = acce}, Some (TArrow (ty,oget acce.ety)), e.espan))
         ts body
     | _ ->
       aexp (efun
               { arg = x;
                 argty = Some xty;
                 resty = body.ety;
                 body = body}, Some (TArrow (xty,oget body.ety)), e.espan))
  | EFun {arg = x; argty = _; resty= _; body= body} ->
    failwith "missing types in function declaration"
  | EApp (e1, e2) ->
    let e2 = flatten_exp e2 in
    (match e2.e with
     | ETuple es ->
       aexp (apps (flatten_exp e1) es, Some (flatten_ty (oget e.ety)), e.espan)
     | _ ->
       aexp (eapp (flatten_exp e1) e2, Some (flatten_ty (oget e.ety)), e.espan))
  | EIf (e1, e2, e3) ->
    aexp (eif (flatten_exp e1) (flatten_exp e2) (flatten_exp e3),
          Some (flatten_ty (oget e.ety)), e.espan)
  | ELet (x, e1, e2) ->
    let e1 = flatten_exp e1 in
    let ty = flatten_ty (oget e.ety) in
    (match e1.e with
     | ETuple es ->
       let es = BatList.mapi (fun i e -> (proj_var i x, e)) es in
       BatList.fold_right (fun (xi, ei) acc ->
           aexp (elet xi ei acc, Some ty, ei.espan)) es (flatten_exp e2)
     | _ ->
       (match (oget e1.ety) with
        | TTuple ts ->
          let ps = BatList.mapi (fun i _ -> PVar (proj_var i x)) ts in
          aexp (ematch e1 (addBranch (PTuple ps) (flatten_exp e2) emptyBranch),
                Some ty, e.espan)
        | _ ->
          aexp (elet x e1 (flatten_exp e2), Some ty, e.espan)))
  | ETuple es ->
    let es = BatList.map flatten_exp es in
    (* Dummy exp which is only used as an argument to wrap *)
    let wrapper = aexp (etuple [], Some (flatten_ty (oget e.ety)), e.espan) in
    (* Extract the elements of e, then call cont to move on to the next e.
       Once we have all of them we'll put them together into one big tuple exp *)
    let curry_elts e (cont : exp list -> exp) =
      match e.e with
      | ETuple es -> cont es
      | EVal v ->
        (match v.v with
         | VTuple vs -> cont (BatList.map e_val vs)
         | _ -> cont [e])
      | _ ->
        match oget e.ety with
        | TTuple tys ->
          (* Tuple type, but not directly a tuple expression. The only way to extract
             its elements is via a match expression. *)
          let freshvars = List.map (fun ty -> ty, Var.fresh "TupleFlattenVar") tys in
          let freshvarexps = List.map (fun (ty, v) -> aexp (evar v, Some ty, e.espan)) freshvars in
          let pat = PTuple (List.map (fun (_, v) -> PVar v) freshvars) in
          let body = cont freshvarexps in
          ematch e (addBranch pat body emptyBranch) |> wrap wrapper
        | _ -> cont [e]
    in
    let rec build_exp lst acc =
      match lst with
      | [] -> etuple (List.rev acc) |> wrap wrapper
      | hd::tl -> curry_elts hd (fun es -> build_exp tl (List.rev_append es acc))
    in
    build_exp es [] |> wrap wrapper
  | ESome e1 ->
    aexp (esome (flatten_exp e1), Some (flatten_ty (oget e.ety)), Span.default)
  | EMatch (e1, bs) ->
    aexp (ematch (flatten_exp e1) (flatten_branches bs ((oget e1.ety))),
          Some (flatten_ty (oget e.ety)),
          e.espan)
  | EOp (op, es) -> (
      match op with
      | And
      | Or
      | Not
      | UAdd _
      | USub _
      | Eq
      | ULess _
      | AtMost _
      | MCreate
      | MGet
      | MSet
      | ULeq _
      | NLess
      | NLeq ->
        aexp (eop op (BatList.map flatten_exp es),
              Some (flatten_ty (oget e.ety)), e.espan)
      | _ -> failwith "TODO: implement tupple flattening for more map operations")
  | ERecord _ | EProject _ -> failwith "Record expression in flattening"

and flatten_branches bs ty =
  let rec flatten_pattern p ty =
    let ty = get_inner_type ty in
    match p with
    | POption (Some p) ->
      (match ty with
       | TOption t ->
         POption (Some (flatten_pattern p t))
       | _ -> failwith "expected option type")
    | PEdge (p1, p2) ->
      flatten_pattern (PTuple [p1; p2]) (TTuple [TNode; TNode])
    | PTuple ps ->
      (match ty with
       | TTuple ts ->
         let ps = BatList.map2 flatten_pattern ps ts in
         let ps' = BatList.fold_right (fun p acc ->
             match p with
             | PTuple ps -> ps @ acc
             | _ -> p :: acc) ps []
         in
         PTuple ps'
       | _ -> failwith "expected tuple type")
    | PVar x ->
      (match ty with
       | TTuple ts ->
         (match flatten_ty (TTuple ts) with
          | TTuple ts ->
            let ps = BatList.mapi (fun i _ -> PVar (proj_var i x)) ts in
            PTuple ps
          | _ -> failwith "must be ttuple")
       | _ -> p)
    | PWild ->
      (match ty with
       | TTuple ts ->
         (match flatten_ty (TTuple ts) with
          | TTuple ts ->
            let ps = BatList.map (fun _ -> PWild) ts in
            PTuple ps
          | _ -> failwith "must be ttuple")
       | _ -> p)
    | PUnit | PBool _ | PInt _ | POption None | PNode _ -> p
    | PRecord _ -> failwith "record pattern in flattening"
  in
  mapBranches (fun (p, e) -> (flatten_pattern p ty, flatten_exp e)) bs

let flatten_symbolic (var, toe) =
  match toe with
  | Exp e ->
    let e = flatten_exp e in
    (match e.e with
     | ETuple es ->
       BatList.mapi (fun i ei -> (proj_var i var, Exp ei)) es
     | _ -> [(var, Exp e)])
  | Ty ty ->
    match flatten_ty ty with
    | TTuple ts ->
      BatList.mapi (fun i ty -> (proj_var i var, Ty ty)) ts
    | ty -> [(var, Ty ty)]

let flatten_decl_single d =
  match d with
  | DLet (x, oty, e) -> DLet (x, Some (flatten_ty (oget oty)), flatten_exp e)
  | DMerge e -> DMerge (flatten_exp e)
  | DTrans e -> DTrans (flatten_exp e)
  | DInit e -> DInit (flatten_exp e)
  | DAssert e -> DAssert (flatten_exp e)
  | DRequire e -> DRequire (flatten_exp e)
  | DATy aty -> DATy (flatten_ty aty)
  | DUserTy (x,ty) -> DUserTy (x, flatten_ty ty)
  | DNodes _ | DEdges _ -> d
  | DSymbolic _ -> failwith "impossible"

(* assumes symbolic expressions are values (no if-then-else etc.)
   maybe they should just be values?*)
let flatten_decl d =
  match d with
  | DSymbolic (x, toe) ->
    let flattened = flatten_symbolic (x, toe) in
    List.map (fun (x, toe) -> DSymbolic (x, toe)) flattened
  | _ -> [flatten_decl_single d]

let flatten ds =
  BatList.map flatten_decl ds |> BatList.concat

let rec unflatten_list (vs : Syntax.value list) (ty : Syntax.ty) =
  match ty with
  | TEdge ->
    begin
      match vs with
      | [{v=VNode n1; _}; {v=VNode n2; _}] -> (vedge (n1, n2)), []
      | _ -> failwith "internal error unflattening edge"
    end
  | TTuple ts ->
    let vs, vleft = BatList.fold_left (fun (vacc, vleft)  ty ->
        let v, vs' = unflatten_list vleft ty in
        (v :: vacc, vs')) ([], vs) ts
    in
    (vtuple (BatList.rev vs)), vleft
  | _ -> BatList.hd vs, BatList.tl vs

let unflatten_val (v : Syntax.value) (ty : Syntax.ty) =
  match v.v with
  | VTuple vs ->
    (match unflatten_list vs ty with
     | v, [] -> v
     | _, vleft ->
       Printf.printf "%s" (printList (Printing.value_to_string) vleft "" "\n" "\n");
       failwith "incorrect unflattening, leftover list should be empty")
  | _ -> v

let unproj_symbolics (symbs : value VarMap.t) : value VarMap.t=
  let unboxed_map =
    VarMap.fold
      (fun var v acc ->
         let (index, var') =
           try unproj_var var
           with Not_found -> (0, var)
         in
         VarMap.modify_def [] var'
           (fun xs -> (index,v) :: xs) acc )
      symbs
      VarMap.empty
  in
  (* Transform our lists of (index, value) pairs into the corresponding tuples *)
  VarMap.map
    (fun elts ->
       match elts with
       | [] -> failwith "Impossible"
       | [(0, v)] -> v
       | lst ->
         let lst = BatList.sort (fun a b -> compare (fst a) (fst b)) lst in
         (* Sanity check *)
         assert (BatList.fold_lefti (fun acc i elt -> acc && (i = fst elt)) true lst);
         vtuple (BatList.map snd lst)
    )
    unboxed_map

let unflatten_sol
    (orig_attr: Syntax.ty)
    (sym_types: Syntax.ty VarMap.t)
    (sol : Solution.t) =
  { sol with
    labels = AdjGraph.VertexMap.map (fun v -> unflatten_val v orig_attr) sol.labels;
    symbolics = VarMap.mapi (fun x v ->
        unflatten_val v (VarMap.find x sym_types)) (unproj_symbolics sol.symbolics)
  }

let flatten_net net =
  { attr_type = flatten_ty net.attr_type;
    init = flatten_exp net.init;
    trans = flatten_exp net.trans;
    merge = flatten_exp net.merge;
    assertion = (match net.assertion with
        | None -> None
        | Some e -> Some (flatten_exp e));
    symbolics =
      BatList.map flatten_symbolic net.symbolics |> BatList.concat;
    defs =
      BatList.map (fun (x, oty, e) ->
          (x, Some (flatten_ty (oget oty)), flatten_exp e)) net.defs;
    utys =
      BatList.map (fun m ->
          Collections.StringMap.map flatten_ty m) net.utys;
    requires = BatList.map (flatten_exp) net.requires;
    graph = net.graph
  }, unflatten_sol net.attr_type
    (BatList.fold_left (fun acc (x,exp_ty) ->
         VarMap.add x (get_ty_from_tyexp exp_ty) acc)
        VarMap.empty net.symbolics)


let flatten_srp srp =
  let flatten_attr = flatten_ty srp.srp_attr in
  { srp_attr = flatten_attr;
    srp_constraints = AdjGraph.VertexMap.map flatten_exp srp.srp_constraints;
    srp_labels =
      AdjGraph.VertexMap.map
        (fun xs -> let var, _ = BatList.hd xs in (* this will be a singleton list*)
          match flatten_attr with
          | TTuple ts ->
            BatList.mapi (fun i ty -> (proj_var i var, ty)) ts
          | ty -> [(var, ty)]
        ) srp.srp_labels;
    srp_assertion = (match srp.srp_assertion with
        | None -> None
        | Some e -> Some (flatten_exp e));
    srp_symbolics =
      BatList.map flatten_symbolic srp.srp_symbolics |> BatList.concat;
    srp_requires = BatList.map (flatten_exp) srp.srp_requires;
    srp_graph = srp.srp_graph
  }, unflatten_sol srp.srp_attr
    (BatList.fold_left (fun acc (x,exp_ty) ->
         VarMap.add x (get_ty_from_tyexp exp_ty) acc)
        VarMap.empty srp.srp_symbolics)
