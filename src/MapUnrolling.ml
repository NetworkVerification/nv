open Collections
open Solution
open Syntax
open Visitors

module ExprSet = Set.Make (struct
  type t = string * exp

  let compare (_, a) (_, b) = compare a b
end)

let rec repeat x i = if i = 0 then [] else x :: repeat x (i - 1)

let tuple_count tymap ty =
  let ty = Typing.strip_ty ty in
  match TypeMap.find_opt ty tymap with
  | None -> 0
  | Some es -> List.length es

let create_pattern_names count =
  let names = ref [] in
  List.iteri
    (fun i x ->
      let name = Var.fresh x |> Var.to_string in
      names := name :: !names )
    (repeat "p" count) ;
  List.rev !names

let rec tuplify_ty tymap ty =
  match ty with
  | TVar {contents= Link t} -> tuplify_ty tymap t
  | TBool -> ty
  | TInt _ -> ty
  | TArrow (t1, t2) ->
      TArrow (tuplify_ty tymap t1, tuplify_ty tymap t2)
  | TTuple ts -> TTuple (List.map (tuplify_ty tymap) ts)
  | TOption t -> TOption (tuplify_ty tymap t)
  | TMap (_, ty2) ->
      let t2 = tuplify_ty tymap ty2 in
      let count = tuple_count tymap ty in
      if count = 1 then t2 else TTuple (repeat t2 count)
  | QVar _ | TVar _ -> failwith "internal error (tuplify_ty)"

let rec tuplify_exp tymap e : exp =
  match e.e with
  | EOp (op, es) -> (
    match (op, es) with
    | And, _
     |Or, _
     |Not, _
     |UAdd _, _
     |USub _, _
     |UEq, _
     |ULess _, _
     |ULeq _, _ ->
        eop op (List.map (tuplify_exp tymap) es)
    | MCreate, [e1] ->
        (* createMap n e --> (e,e,e,...) *)
        let ty = oget e.ety in
        let count = tuple_count tymap ty in
        let e1 = tuplify_exp tymap e1 in
        let es = repeat e1 count in
        if count = 1 then List.hd es else etuple es
    | MSet, [e1; e2; e3] -> (
        (* m[e1 := e2] --> (if d = e1 then e2 else m.0, if d_1 = e1 then e2 else m.1, ...) *)
        let ty = oget e.ety in
        match TypeMap.find_opt (Typing.strip_ty ty) tymap with
        | None ->
            (* TODO: what if setter is used in assert statement? *)
            failwith "internal error (tuplify_exp: mset)"
        | Some es ->
            let ks, _ = List.split es in
            let ps, es =
              unpack
                (fun (k, p) ->
                  let keyvar = evar (Var.create k) in
                  let pvar = evar (Var.create p) in
                  let eq = eop UEq [keyvar; tuplify_exp tymap e2] in
                  eif eq (tuplify_exp tymap e3) pvar )
                ks
            in
            let es =
              if List.length es = 1 then List.hd es else etuple es
            in
            let ps =
              if List.length ps = 1 then List.hd ps else PTuple ps
            in
            ematch (tuplify_exp tymap e1) [(ps, es)] )
    | MGet, [e1; e2] -> (
        (* m[e] --> m.i_e  if known index else m.0 *)
        let ty = oget e1.ety in
        match TypeMap.find_opt (Typing.strip_ty ty) tymap with
        | None -> failwith "internal error (tuplify_exp: mget)"
        | Some es ->
            let ps = create_pattern_names (List.length es) in
            let zip = List.combine ps es in
            let entry =
              List.find_opt (fun (p, (_, e)) -> e = e2) zip
            in
            let e =
              match entry with
              | None ->
                  (* TODO: not right yet, something with e2 *)
                  let p = List.hd ps in
                  evar (Var.create p)
              | Some (p, _) -> evar (Var.create p)
            in
            let ps = List.map (fun n -> PVar (Var.create n)) ps in
            let ps =
              if List.length ps = 1 then List.hd ps else PTuple ps
            in
            ematch (tuplify_exp tymap e1) [(ps, e)] )
    | MMap, [e1; e2] ->
        (* map f m --> (f m.0, f m.1, ...) *)
        mk_map tymap e e1 e2 ~filter:None
    | MMapFilter, [e1; e2; e3] ->
        mk_map tymap e e2 e3 ~filter:(Some e1)
    | MMerge, [e1; e2; e3] | MMerge, [e1; e2; e3; _; _; _; _] -> (
        (* merge f m1 m2 --> (f m1.0 m2.0, f m1.1 m2.1, ...) *)
        let ty1, ty2 = (oget e2.ety, oget e3.ety) in
        match
          ( TypeMap.find_opt (Typing.strip_ty ty1) tymap
          , TypeMap.find_opt (Typing.strip_ty ty2) tymap )
        with
        | Some es1, Some es2 ->
            let ks1, _ = List.split es1 in
            let ks2, _ = List.split es2 in
            let ps1, ps2, es =
              unpack2
                (fun (k1, p1) (k2, p2) ->
                  let pvar1 = evar (Var.create p1) in
                  let pvar2 = evar (Var.create p2) in
                  eapp (eapp (tuplify_exp tymap e1) pvar1) pvar2 )
                ks1 ks2
            in
            let es =
              if List.length es = 1 then List.hd es else etuple es
            in
            let ps1 =
              if List.length ps1 = 1 then List.hd ps1 else PTuple ps1
            in
            let ps2 =
              if List.length ps2 = 1 then List.hd ps2 else PTuple ps2
            in
            ematch
              (etuple [tuplify_exp tymap e2; tuplify_exp tymap e3])
              [(PTuple [ps1; ps2], es)]
        | _ -> failwith "internal error (tuplify_exp: mmerge)" )
    | _ -> failwith "internal error (tuplify_exp: no match)" )
  | EFun f ->
      efun
        { f with
          argty= None; resty= None; body= tuplify_exp tymap f.body }
  | EApp (e1, e2) -> failwith ""
  | EIf (e1, e2, e3) ->
      eif (tuplify_exp tymap e1) (tuplify_exp tymap e2)
        (tuplify_exp tymap e3)
  | ELet (x, e1, e2) ->
      elet x (tuplify_exp tymap e1) (tuplify_exp tymap e2)
  | ETuple es -> etuple (List.map (tuplify_exp tymap) es)
  | ESome e -> esome (tuplify_exp tymap e)
  | EMatch (e, bs) ->
      ematch (tuplify_exp tymap e) (tuplify_branches tymap bs)
  | ETy (e, ty) -> tuplify_exp tymap e
  | EVal _ -> (* no way to construct a map value directly *) exp e.e
  | EVar _ -> exp e.e

and mk_map tymap e e1 e2 ~filter =
  let ty = oget e.ety in
  match TypeMap.find_opt (Typing.strip_ty ty) tymap with
  | None -> failwith "internal error (tuplify_exp: mmap)"
  | Some es ->
      let ks, _ = List.split es in
      let ps, es =
        unpack
          (fun (k, p) ->
            let key = evar (Var.create k) in
            let pvar = evar (Var.create p) in
            let ea = eapp (tuplify_exp tymap e1) pvar in
            match filter with
            | None -> ea
            | Some e3 ->
                let cond = eapp (tuplify_exp tymap e3) key in
                eif cond ea pvar )
          ks
      in
      let es =
        if List.length es = 1 then List.hd es else etuple es
      in
      let ps =
        if List.length ps = 1 then List.hd ps else PTuple ps
      in
      ematch (tuplify_exp tymap e2) [(ps, es)]

(* no way to pattern match a map, so just keep patterns *)
and tuplify_branches tymap bs =
  List.map (fun (p, e) -> (p, tuplify_exp tymap e)) bs

and unpack f ks =
  let count = List.length ks in
  let names = create_pattern_names count in
  let es = List.combine ks names |> List.map f in
  let ps = List.map (fun n -> PVar (Var.create n)) names in
  (ps, es)

and unpack2 f ks1 ks2 =
  let count = List.length ks1 in
  let names1 = create_pattern_names count in
  let names2 = create_pattern_names count in
  let zip1 = List.combine ks1 names1 in
  let zip2 = List.combine ks2 names2 in
  let all = List.combine zip1 zip2 in
  let es = List.map (fun (x, y) -> f x y) all in
  let ps1 = List.map (fun n -> PVar (Var.create n)) names1 in
  let ps2 = List.map (fun n -> PVar (Var.create n)) names2 in
  (ps1, ps2, es)

let tuplify_decl tymap d =
  match d with
  | DLet (x, oty, e) -> DLet (x, oty, tuplify_exp tymap e)
  | DMerge e -> DMerge (tuplify_exp tymap e)
  | DTrans e -> DTrans (tuplify_exp tymap e)
  | DInit e -> DInit (tuplify_exp tymap e)
  | DAssert e -> DAssert (tuplify_exp tymap e)
  | DRequire e -> DRequire (tuplify_exp tymap e)
  | DSymbolic (x, Exp e) -> DSymbolic (x, Exp (tuplify_exp tymap e))
  | DSymbolic (x, Ty ty) -> DSymbolic (x, Ty (tuplify_ty tymap ty))
  | DATy aty -> DATy (tuplify_ty tymap aty)
  | DNodes _ | DEdges _ -> d

let tuplify tymap ds = List.map (tuplify_decl tymap) ds

let update_with tymap ty e =
  try
    let es = TypeMap.find (Typing.strip_ty ty) tymap in
    TypeMap.add ty (ExprSet.add e es) tymap
  with _ -> TypeMap.add ty (ExprSet.singleton e) tymap

(* Returns all occurences of map types in the program *)
let collect_all_map_tys ds =
  let all_tys = ref TypeMap.empty in
  let f d e =
    let ty = Typing.strip_ty (oget e.ety) in
    match get_inner_type ty with
    | TMap _ -> all_tys := TypeMap.add ty () !all_tys
    | _ -> ()
  in
  Visitors.iter_exp_decls f ds ;
  !all_tys

let collect_map_gets ds map =
  let f d e =
    match (d, e.e) with
    (* | DAssert _, _ -> () *)
    | _, EOp (MGet, [e1; e2]) ->
        let symkey = Var.fresh "key" |> Var.to_string in
        map :=
          update_with !map
            (oget e1.ety |> Typing.strip_ty)
            (symkey, e2)
    | _ -> ()
  in
  Visitors.iter_exp_decls f ds ;
  !map

let sort_keys es =
  ExprSet.elements es
  |> List.stable_sort (fun (k1, _) (k2, _) -> compare k1 k2)

let lookup s sol =
  StringMap.find (Var.create s |> Var.to_string) sol.symbolics

let build_value_map sol acc (vv, (s, _)) =
  BddMap.update acc (lookup s sol) vv

let drop_syms variables s _ =
  List.exists
    (fun (_, k, _) -> String.equal (Var.to_string k) s)
    variables
  |> not

let map_back orig_sym_types (map: ExprSet.elt list TypeMap.t)
    variables ds (sol: Solution.t) : Solution.t =
  let rec aux ty v : value =
    let ty = Typing.strip_ty ty in
    match (ty, v.v) with
    | TMap (ty1, ty2), _ -> (
        let es = TypeMap.find ty map in
        let default = default_value ty2 in
        let base = BddMap.create ~key_ty:ty1 default in
        match (v.v, es) with
        | VTuple vs, _ ->
            let zip = List.combine vs es in
            let map =
              List.fold_left (build_value_map sol) base zip
            in
            vmap map
        | _, [(s, _)] ->
            let map = BddMap.update base (lookup s sol) v in
            vmap map
        | _ -> failwith "internal error (map_back1)" )
    | TBool, VBool _ -> v
    | TInt _, VInt _ -> v
    | TOption t, VOption None -> v
    | TOption t, VOption (Some v) -> voption (Some (aux t v))
    | TTuple ts, VTuple vs ->
        let vs =
          List.map (fun (t, v) -> aux t v) (List.combine ts vs)
        in
        vtuple vs
    | _ -> failwith "internal error (map_back)"
  in
  let aty = oget (get_attr_type ds) |> Typing.strip_ty in
  let update_labels ls =
    AdjGraph.VertexMap.map (fun v -> aux aty v) ls
  in
  let update_symbolics sol =
    let syms =
      StringMap.filter (drop_syms variables) sol.symbolics
    in
    StringMap.mapi
      (fun k v -> aux (StringMap.find k orig_sym_types) v)
      syms
  in
  { sol with
    labels= update_labels sol.labels; symbolics= update_symbolics sol
  }

let collect_all_symbolics_d d =
  match d with
  | DSymbolic (x, Exp e) ->
      StringMap.singleton (Var.to_string x) (oget e.ety)
  | DSymbolic (x, Ty ty) -> StringMap.singleton (Var.to_string x) ty
  | _ -> StringMap.empty

let rec collect_all_symbolics ds =
  match ds with
  | [] -> StringMap.empty
  | d :: ds ->
      StringMap.merge
        (fun _ _ _ -> None)
        (collect_all_symbolics_d d)
        (collect_all_symbolics ds)

exception Cannot_unroll of exp

let check_constants (map: ExprSet.t TypeMap.t) vars =
  TypeMap.iter
    (fun _ es ->
      ExprSet.iter
        (fun (_, e) ->
          match e.e with
          | EVal _ -> ()
          | EVar v when VarSet.mem v vars -> ()
          | _ -> raise (Cannot_unroll e) )
        es )
    map

let unroll info ds =
  let orig_sym_types = collect_all_symbolics ds in
  let map = ref TypeMap.empty in
  let all_tys = collect_all_map_tys ds in
  let vars = ref VarSet.empty in
  TypeMap.iter
    (fun ty _ ->
      let var = Var.fresh "dkey" in
      vars := VarSet.add var !vars ;
      let e = ExprSet.singleton (Var.to_string var, evar var) in
      map := TypeMap.add ty e !map )
    all_tys ;
  let map = collect_map_gets ds map in
  check_constants map !vars ;
  let map = TypeMap.map sort_keys map in
  let decls = tuplify map ds in
  let variables =
    TypeMap.fold
      (fun ty es acc ->
        List.map (fun (x, y) -> (ty, Var.create x, y)) es @ acc )
      map []
  in
  let symbolics =
    List.map
      (fun (ty, x, _) ->
        match get_inner_type ty with
        | TMap (ty, _) -> DSymbolic (x, Ty (tuplify_ty map ty))
        | _ -> failwith "internal error (unroll)" )
      variables
  in
  let vs =
    List.filter
      (fun (_, s, _) -> String.sub (Var.name s) 0 1 <> "d")
      variables
  in
  let vs = List.map (fun (_, s, e) -> (s, e)) vs in
  let decls = symbolics @ decls in
  (* print_endline (Printing.declarations_to_string decls) ; *)
  ( Typing.infer_declarations info decls
  , vs
  , map_back orig_sym_types map variables ds )
