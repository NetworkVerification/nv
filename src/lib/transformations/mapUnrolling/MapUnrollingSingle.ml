open Batteries
open Nv_lang
open Syntax
open Typing
open Collections
open Nv_datastructures
open Nv_utils.OCamlUtils
open Nv_solution

type keys = (exp list) * (var list)

let has_target_type (target : ty) (e : exp) : bool =
  equal_inner_tys target (oget e.ety)
;;

let get_index_const (keys : keys) (k : exp) =
  let const_keys, _ = keys in
  try
    let index, _ =
      List.findi (fun _ e -> compare_es e k = 0) const_keys
    in
    Some(index)
  with
  | _ -> None
;;

let get_index_symb (keys : keys) (symb : var) =
  let const_keys, symb_keys = keys in
  try
    let index, _ =
      List.findi (fun _ s -> Var.equal s symb) symb_keys
    in
    Some(index + List.length const_keys)
  with
  | _ -> None
;;

let ty_transformer (target : ty) (keys : keys) _ ty =
  (* let ty = canonicalize_type ty in *)
  match ty with
  | TMap(_, vty) ->
    if equal_inner_tys target ty then
      let const_keys, symb_keys = keys in
      (* Don't need to recurse since types cannot contain themselves *)
      Some (TTuple (List.make (List.length const_keys + List.length symb_keys) vty))
    else
      None
  (* | QVar _ -> Some ty *)
  | _ -> None
;;

(* No such thing as a map pattern *)
let pattern_transformer _ p _ = Some p;;

let value_transformer _ v =
  match v.v with
  | VMap _ -> failwith "This should be impossible, but if not we'll have to implement it"
  | _ -> None
;;

let rec unroll_get_or_set
    (keys : keys)
    (mk_op : int -> exp)
    (etype : ty option)
    (espan : Span.t)
    (k : exp) =
  let get_index_const = get_index_const keys in
  let get_index_symb = get_index_symb keys in
  match get_index_const k with
  | Some n ->
    (* Constant key - no need to write a match *)
    mk_op n
  | None ->
    let const_keys, symb_keys = keys in
    let const_branches =
      const_keys
      |> List.mapi
        (fun i k -> (exp_to_pattern k, mk_op i))
      |> List.fold_left
        (fun acc (p,x) -> addBranch p x acc)
        emptyBranch
    in
    match get_inner_type (oget k.ety) with
    | TNode
    | TEdge ->
      (* We know all possible node and edge values in advance, so just
         match the key with each of them *)
      ematch k const_branches
    | _ ->
      (* Otherwise, we require that the key be a symbolic variable *)
      let index =
        match k.e with
        | EVar v ->
          begin
            match get_index_symb v with
            | Some i -> i
            | None -> failwith @@
              "Encountered non-constant, non-symbolic variable key whose type is not TNode or TEdge: " ^
              Printing.exp_to_string k ^ ", type: " ^ Printing.ty_to_string (oget k.ety)
          end
        | _ -> failwith @@
          "Encountered non-constant, non-variable key whose type is not TNode or TEdge: " ^
          Printing.exp_to_string k
      in
      (* List of symbolics with a strictly lower index *)
      let preceding_symb_keys =
        List.take index symb_keys
      in
      let big_if =
        List.fold_left
          (fun acc v ->
             let cmp =
               (* Compare our key to the symbolic variable v *)
               aexp (eop Eq [k; aexp (evar v, k.ety, k.espan)], Some TBool, espan)
             in
             let ethen =
               (* If they're the same value, use v's index instead of k's *)
               v |> get_index_symb |> oget |> mk_op
             in
             aexp (eif cmp ethen acc, etype, espan)
          )
          (* If we have a different value from all the lower-index symbolics,
             use our own index *)
          (mk_op index)
          preceding_symb_keys
      in
      let final_branches = addBranch PWild big_if const_branches in
      ematch k final_branches
;;

let exp_transformer (target : ty) (keys : keys) (recursors : Transformers.recursors) e =
  let unroll_type = recursors.recurse_ty in
  let unroll_exp = recursors.recurse_exp in
  let has_target_type = has_target_type target in

  let unrolled_target = unroll_type target in
  let const_keys, symb_keys = keys in

  let unrolled_size = List.length const_keys + List.length symb_keys in
  match e.e with
  | EOp (op, es) ->
    begin
      match op, es with
      | MCreate, [e1] when has_target_type e ->
        Some (etuple (List.make unrolled_size (unroll_exp e1)))
      | MGet, [map; k] when has_target_type map ->
        let unrolled_map = unroll_exp map in
        let unrolled_ety = omap unroll_type e.ety in
        let mk_op =
          (fun index ->
             aexp (eop (TGet (unrolled_size, index, index)) [unrolled_map],
                   unrolled_ety, e.espan))
        in
        Some (unroll_get_or_set keys mk_op unrolled_ety e.espan k)
      | MSet, [map; k; setval] when has_target_type map ->
        let unrolled_map = unroll_exp map in
        let unrolled_setval = unroll_exp setval in
        let unrolled_ety = omap unroll_type e.ety in
        let mk_op =
          (fun index ->
             aexp (eop (TSet (unrolled_size, index, index)) [unrolled_map; unrolled_setval],
                   unrolled_ety, e.espan))
        in
        Some (unroll_get_or_set keys mk_op unrolled_ety e.espan k)
      | MMap, [f; map] when has_target_type map->
        let val_ty =
          match target (* Type of the map we're unrolling *) with
          | TMap (_, ty) -> ty
          | _ -> failwith "impossible"
        in
        let f' = unroll_exp f in
        let freshvars =
          List.map (fun _ -> Var.fresh "UnrollingMapVar") symb_keys @
          List.map (fun _ -> Var.fresh "UnrollingMapVar") const_keys
        in
        let pattern =
          PTuple (List.map (fun var -> PVar var) freshvars)
        in
        let freshvars =
          List.map (fun var -> aexp (evar var, Some (val_ty), e.espan)) freshvars
        in
        let result =
          List.map
            (fun var -> aexp (eapp f' var, Some (val_ty), e.espan))
            freshvars
        in
        Some (ematch (unroll_exp map) (addBranch pattern (aexp ((etuple result), Some (unrolled_target), e.espan)) emptyBranch))
      | MMapFilter, [p; f; map] when has_target_type map ->
        let key_ty =
          match target (* Type of the map we're unrolling *) with
          | TMap (ty, _) -> ty
          | _ -> failwith "impossible"
        in
        let f' = unroll_exp f in
        let p' = unroll_exp p in
        let all_keys =
          List.map (fun v -> aexp (evar v, Some key_ty, e.espan)) symb_keys @
          const_keys
        in
        let freshvars =
          List.map (fun _ -> Var.fresh "UnrollingMapFilterVar") all_keys
        in
        let pattern =
          PTuple (List.map (fun var -> PVar var) freshvars)
        in
        let val_ty =
          match target (* Type of the map we're unrolling *) with
          | TMap (_, ty) -> ty
          | _ -> failwith "impossible"
        in
        let make_result k var =
          let if_exp =
            eif
              (aexp (eapp p' k, Some (TBool), e.espan))
              (aexp (eapp f' var, Some (val_ty), e.espan))
              var
          in
          aexp (if_exp, Some (val_ty), e.espan)
        in
        let freshvars =
          List.map (fun var -> aexp (evar var, Some (val_ty), e.espan)) freshvars
        in
        let result =
          List.map2 make_result all_keys freshvars
        in
        Some (ematch (unroll_exp map) (addBranch pattern (aexp ((etuple result), Some (unrolled_target), e.espan)) emptyBranch))
      | MMapIte, [p; f1; f2; map] when has_target_type map ->
        let key_ty =
          match target (* Type of the map we're unrolling *) with
          | TMap (ty, _) -> ty
          | _ -> failwith "impossible"
        in
        let f1' = unroll_exp f1 in
        let f2' = unroll_exp f2 in
        let p' = unroll_exp p in
        let all_keys =
          List.map (fun v -> aexp (evar v, Some key_ty, e.espan)) symb_keys @
          const_keys
        in
        let freshvars =
          List.map (fun _ -> Var.fresh "UnrollingMapFilterVar") all_keys
        in
        let pattern =
          PTuple (List.map (fun var -> PVar var) freshvars)
        in
        let val_ty =
          match target (* Type of the map we're unrolling *) with
          | TMap (_, ty) -> ty
          | _ -> failwith "impossible"
        in
        let make_result k var =
          let if_exp =
            eif
              (aexp (eapp p' k, Some (TBool), e.espan))
              (aexp (eapp f1' var, Some (val_ty), e.espan))
              (aexp (eapp f2' var, Some (val_ty), e.espan))
          in
          aexp (if_exp, Some (val_ty), e.espan)
        in
        let freshvars =
          List.map (fun var -> aexp (evar var, Some (val_ty), e.espan)) freshvars
        in
        let result =
          List.map2 make_result all_keys freshvars
        in
        Some (ematch (unroll_exp map) (addBranch pattern (aexp ((etuple result), Some (unrolled_target), e.espan)) emptyBranch))
      | MMerge, f :: map1 :: map2 :: _ when has_target_type map1 && has_target_type map2 ->
        (* Should be redundant, since I think typing assumes the arguments to
           MMerge have the same type *)
        let f' = unroll_exp f in
        let val_ty =
          match target (* Map type we're unrolling *) with
          | TMap (_, ty) -> ty
          | _ -> failwith "impossible"
        in
        let freshvars1, freshvars2 =
          let lst =
            List.make (List.length symb_keys + List.length const_keys) ()
          in
          List.map (fun _ -> Var.fresh "UnrollingMergeVar1") lst,
          List.map (fun _ -> Var.fresh "UnrollingMergeVar2") lst
        in
        let pattern =
          PTuple([
              PTuple (List.map (fun var -> PVar var) freshvars1);
              PTuple (List.map (fun var -> PVar var) freshvars2)
            ])
        in
        let result =
          List.map2
            (fun var1 var2 ->
               let v1 = aexp (evar var1, Some (val_ty), e.espan) in
               let v2 = aexp (evar var2, Some (val_ty), e.espan) in
               let fst_app =
                 aexp ((eapp f' v1), Some (TArrow (val_ty, val_ty)), e.espan)
               in
               aexp (eapp fst_app v2, Some (val_ty), e.espan))
            freshvars1 freshvars2
        in
        let map_pair =
          aexp
            ((etuple [unroll_exp map1; unroll_exp map2]),
             Some (TTuple [unroll_type target; unroll_type target]),
             e.espan)
        in
        Some (
          ematch
            map_pair
            (addBranch pattern (aexp ((etuple result), Some (unrolled_target), e.espan)) emptyBranch))
      | MFoldNode, [f; map; acc]
      | MFoldEdge, [f; map; acc] when has_target_type map ->
        (* fold f acc m ->
           (f (f acc k1 v1) k2 v2)
        *)
        let key_ty, val_ty =
          match target (* Type of the map we're unrolling *) with
          | TMap (kty, vty) -> kty, vty
          | _ -> failwith "impossible"
        in
        let acc' = unroll_exp acc in
        let acc_ty = oget acc'.ety in
        let f' = unroll_exp f in
        let symb_var_keys =
          List.map (fun v -> aexp (evar v, Some key_ty, e.espan)) symb_keys
        in
        let freshvars =
          List.map (fun k -> (k, Var.fresh "UnrollingFoldVar")) (symb_var_keys @ const_keys)
        in
        let pattern =
          PTuple (List.map (fun (_, var) -> PVar var) freshvars)
        in
        let fold_vars =
          List.map (fun (k, v) -> k, aexp (evar v, Some (val_ty), e.espan)) freshvars
        in
        let result =
          List.fold_left
            (fun acc (k, v) ->
               let app1 = aexp (eapp f' k, Some (TArrow (val_ty, TArrow(acc_ty, acc_ty))), e.espan) in
               let app2 = aexp (eapp app1 v, Some (TArrow(acc_ty, acc_ty)), e.espan) in
               let app3 = aexp (eapp app2 acc, Some (acc_ty), e.espan) in
               app3)
            acc'
            fold_vars
        in
        Some (ematch (unroll_exp map) (addBranch pattern result emptyBranch))
      (* Do some extra work to make sure all map operations have the right number of arguments *)
      | (MCreate, [_] | MGet, [_; _] | MSet, [_;_;_] | MMap, [_;_]
        | MMapFilter, [_;_;_] | MMerge, _::_::_::_ | MFoldNode, [_;_;_]
        | MFoldEdge, [_;_;_] | MMapIte, [_;_;_;_]) ->
        None
      | (MCreate| MGet| MSet| MMap| MMapFilter| MMapIte | MMerge | MFoldNode| MFoldEdge), _ ->
        failwith @@ "Failed to unroll map: Incorrect number of arguments to map operation : "
                    ^ Printing.exp_to_string e
      | (AtMost _ | And | Or | Not | UAdd _ | USub _ | UAnd _ | ULess _ | ULeq _ | NLess | NLeq | Eq | TGet _ | TSet _), _ -> None
    end
  | _ -> None
;;

let map_back_transformer (keys : keys) _ (sol : Solution.t) v orig_ty =
  match v.v, orig_ty with
  | VTuple vs, TMap (kty, vty) ->
    (* We found a converted map; convert it back *)
    let const_keys, symb_keys = keys in
    let default = Nv_lang.Generators.default_value vty in
    let e_vs, symb_vs = BatList.takedrop (List.length const_keys) vs in
    let e_bindings = List.combine (List.map exp_to_value const_keys) e_vs in
    let v_bindings = List.combine (List.map (fun v -> List.assoc v sol.symbolics) symb_keys) symb_vs in
    let bindings = List.rev_append v_bindings e_bindings in
    let newmap = BddMap.from_bindings ~key_ty:kty (bindings, default) in
    Some (vmap newmap)
  | _ -> None
;;

let mask_transformer = map_back_transformer;;


let make_toplevel (target : ty) (keys : keys) (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer ~name:"MapUnrolling" (ty_transformer target keys) pattern_transformer value_transformer
    (exp_transformer target keys) (map_back_transformer keys) (mask_transformer keys)
;;

let unroll_declarations target keys = make_toplevel target keys Transformers.transform_declarations
let unroll_net target keys = make_toplevel target keys Transformers.transform_network
let unroll_srp target keys = make_toplevel target keys Transformers.transform_srp
