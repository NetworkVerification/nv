open Syntax
open Visitors

module ExprSet = Set.Make (struct
  type t = string * exp

  let compare (_, a) (_, b) = compare a b
end)

module TypeMap = Map.Make (struct
  type t = ty

  let compare = compare
end)

let rec repeat x i = if i = 0 then [] else x :: repeat x (i - 1)

let rec strip_ty ty =
  match ty with
  | TVar {contents= Link t} -> strip_ty t
  | TBool | TInt _ -> ty
  | TArrow (t1, t2) -> TArrow (strip_ty t1, strip_ty t2)
  | TTuple ts -> TTuple (List.map strip_ty ts)
  | TOption t -> TOption (strip_ty t)
  | TMap (ty1, ty2) -> TMap (strip_ty ty1, strip_ty ty2)
  | QVar _ | TVar _ -> Console.error "internal error (strip_ty)"

let tuple_count tymap ty =
  let es = TypeMap.find (strip_ty ty) tymap in
  List.length es

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
  | TArrow (t1, t2) -> TArrow (tuplify_ty tymap t1, tuplify_ty tymap t2)
  | TTuple ts -> TTuple (List.map (tuplify_ty tymap) ts)
  | TOption t -> TOption (tuplify_ty tymap t)
  | TMap (_, ty2) ->
      let t2 = tuplify_ty tymap ty2 in
      let count = tuple_count tymap ty in
      if count = 1 then t2 else TTuple (repeat t2 count)
  | QVar _ | TVar _ -> Console.error "internal error (tuplify_ty)"

let rec tuplify_exp tymap e : exp =
  match e.e with
  | EOp (op, es) -> (
    match (op, es) with
    | And, _ | Or, _ | Not, _ | UAdd, _ | USub, _ | UEq, _ | ULess, _ | ULeq, _ ->
        EOp (op, List.map (tuplify_exp tymap) es) |> exp
    | MCreate, [e1] ->
        (* createMap n e --> (e,e,e,...) *)
        let ty = oget e.ety in
        let count = tuple_count tymap ty in
        let e1 = tuplify_exp tymap e1 in
        let es = repeat e1 count in
        if count = 1 then List.hd es else ETuple es |> exp
    | MSet, [e1; e2; e3] -> (
        (* m[e1 := e2] --> (if d = e1 then e2 else m.0, if d_1 = e1 then e2 else m.1, ...) *)
        let ty = oget e.ety in
        match TypeMap.find_opt (strip_ty ty) tymap with
        | None ->
            (* TODO: what if setter is used in assert statement? *)
            Console.error "internal error (tuplify_exp)"
        | Some es ->
            let ks, _ = List.split es in
            let ps, es =
              unpack
                (fun (k, p) ->
                  let keyvar = EVar (Var.create k) |> exp in
                  let pvar = EVar (Var.create p) |> exp in
                  let eq = EOp (UEq, [keyvar; tuplify_exp tymap e2]) |> exp in
                  EIf (eq, tuplify_exp tymap e3, pvar) |> exp )
                ks
            in
            let es =
              if List.length es = 1 then List.hd es else ETuple es |> exp
            in
            let ps = if List.length ps = 1 then List.hd ps else PTuple ps in
            EMatch (tuplify_exp tymap e1, [(ps, es)]) |> exp )
    | MGet, [e1; e2] -> (
        (* m[e] --> m.i_e  if known index else m.0 *)
        let ty = oget e1.ety in
        match TypeMap.find_opt (strip_ty ty) tymap with
        | None -> Console.error "internal error (tuplify_exp)"
        | Some es ->
            let ps = create_pattern_names (List.length es) in
            let zip = List.combine ps es in
            let entry = List.find_opt (fun (p, (_, e)) -> e = e2) zip in
            let e =
              match entry with
              | None ->
                  (* TODO: not right yet, something with e2 *)
                  let p = List.hd ps in
                  EVar (Var.create p) |> exp
              | Some (p, _) -> EVar (Var.create p) |> exp
            in
            let ps = List.map (fun n -> PVar (Var.create n)) ps in
            let ps = if List.length ps = 1 then List.hd ps else PTuple ps in
            EMatch (tuplify_exp tymap e1, [(ps, e)]) |> exp )
    | MMap, [e1; e2] -> (
        (* map f m --> (f m.0, f m.1, ...) *)
        let ty = oget e.ety in
        match TypeMap.find_opt (strip_ty ty) tymap with
        | None -> Console.error "internal error (tuplify_exp)"
        | Some es ->
            let ks, _ = List.split es in
            let ps, es =
              unpack
                (fun (k, p) ->
                  let pvar = EVar (Var.create p) |> exp in
                  EApp (tuplify_exp tymap e1, pvar) |> exp )
                ks
            in
            let es =
              if List.length es = 1 then List.hd es else ETuple es |> exp
            in
            let ps = if List.length ps = 1 then List.hd ps else PTuple ps in
            EMatch (tuplify_exp tymap e2, [(ps, es)]) |> exp )
    | MMerge, [e1; e2; e3] -> (
        (* merge f m1 m2 --> (f m1.0 m2.0, f m1.1 m2.1, ...) *)
        let ty1, ty2 = (oget e2.ety, oget e3.ety) in
        match
          ( TypeMap.find_opt (strip_ty ty1) tymap
          , TypeMap.find_opt (strip_ty ty2) tymap )
        with
        | Some es1, Some es2 ->
            let ks1, _ = List.split es1 in
            let ks2, _ = List.split es2 in
            let ps1, ps2, es =
              unpack2
                (fun (k1, p1) (k2, p2) ->
                  let pvar1 = EVar (Var.create p1) |> exp in
                  let pvar2 = EVar (Var.create p2) |> exp in
                  EApp (EApp (tuplify_exp tymap e1, pvar1) |> exp, pvar2)
                  |> exp )
                ks1 ks2
            in
            let es =
              if List.length es = 1 then List.hd es else ETuple es |> exp
            in
            let ps1 =
              if List.length ps1 = 1 then List.hd ps1 else PTuple ps1
            in
            let ps2 =
              if List.length ps2 = 1 then List.hd ps2 else PTuple ps2
            in
            EMatch
              ( ETuple [tuplify_exp tymap e2; tuplify_exp tymap e3] |> exp
              , [(PTuple [ps1; ps2], es)] )
            |> exp
        | _ -> Console.error "internal error (tuplify_exp)" )
    | MFilter, [e1; e2] -> failwith ""
    | _ -> Console.error "internal error (tuplify_exp)" )
  | EFun f ->
      EFun {f with argty= None; resty= None; body= tuplify_exp tymap f.body}
      |> exp
  | EApp (e1, e2) -> failwith ""
  | EIf (e1, e2, e3) ->
      EIf (tuplify_exp tymap e1, tuplify_exp tymap e2, tuplify_exp tymap e3)
      |> exp
  | ELet (x, e1, e2) ->
      ELet (x, tuplify_exp tymap e1, tuplify_exp tymap e2) |> exp
  | ETuple es -> ETuple (List.map (tuplify_exp tymap) es) |> exp
  | ESome e -> ESome (tuplify_exp tymap e) |> exp
  | EMatch (e, bs) ->
      EMatch (tuplify_exp tymap e, tuplify_branches tymap bs) |> exp
  | ETy (e, ty) -> tuplify_exp tymap e
  | EVal _ -> (* no way to construct a map value directly *) exp e.e
  | EVar _ -> exp e.e

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
  (* is this right? *)
  | DSymbolic (x, e) -> DSymbolic (x, e)
  | DATy aty -> DATy (tuplify_ty tymap aty)
  | DNodes _ | DEdges _ -> d

let tuplify tymap ds = List.map (tuplify_decl tymap) ds

let update_with tymap ty e =
  try
    let es = TypeMap.find (strip_ty ty) tymap in
    TypeMap.add ty (ExprSet.add e es) tymap
  with _ -> TypeMap.add ty (ExprSet.singleton e) tymap

let collect_all_map_tys ds =
  let all_tys = ref TypeMap.empty in
  let f d e =
    let ty = strip_ty (oget e.ety) in
    match Typing.get_inner_type ty with
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
        map := update_with !map (oget e1.ety |> strip_ty) (symkey, e2)
    | _ -> ()
  in
  Visitors.iter_exp_decls f ds ;
  !map

let sort_keys es =
  ExprSet.elements es |> List.stable_sort (fun (k1, _) (k2, _) -> compare k1 k2)

(* collect a map from type to set of expressions *)
let unroll info ds =
  let all_tys = collect_all_map_tys ds in
  let map = ref TypeMap.empty in
  TypeMap.iter
    (fun ty _ ->
      let var = Var.fresh "dkey" in
      let e = ExprSet.singleton (Var.to_string var, EVar var |> exp) in
      map := TypeMap.add ty e !map )
    all_tys ;
  let map = collect_map_gets ds map in
  let map = TypeMap.map sort_keys map in
  (* TypeMap.iter
    (fun k v ->
      Printf.printf "key: %s\n" (Printing.ty_to_string k) ;
      List.iter
        (fun (k, e) ->
          Printf.printf "  value: (%s,%s)\n" k (Printing.exp_to_string e) )
        v )
    map ; *)
  let ds = tuplify map ds in
  (* TODO: FIXME *)
  let zero = EVal (VUInt32 (Unsigned.UInt32.of_int 0) |> value) |> exp in
  let variables = TypeMap.fold (fun _ es acc -> es @ acc) map [] in
  let symbolics = List.map (fun (k, e) -> Var.create k) variables in
  let symbolics = List.map (fun x -> DSymbolic (x, zero)) symbolics in
  let variables =
    List.filter (fun (s, _) -> String.sub s 0 1 <> "d") variables
  in
  let variables = List.map (fun (s, e) -> (Var.create s, e)) variables in
  let ds = symbolics @ ds in
  (* print_endline (Printing.declarations_to_string ds) ; *)
  (Typing.infer_declarations info ds, variables)
