open Batteries
open Syntax
open Cudd
open BatSet
open Nv_datastructures
open Nv_utils
open OCamlUtils

(* TODO: optimize variable ordering  *)
type t = mtbdd

module B = BddUtils

(* let res = User.map_op2
   ~commutative:true ~idempotent:true
   ~special:(fun bdd1 bdd2 ->
    if Vdd.is_cst bdd1 && Vdd.dval bdd1 = false then Some(bdd1)
    else if Vdd.is_cst bdd2 && Vdd.dval bdd2 = false then Some(bdd2)
    else None)
   (fun b1 b2 -> b1 && b2) *)

let create ~key_ty:ty (v: value) : t =
  B.set_size (B.ty_to_size ty) ;
  (Mtbdd.cst B.mgr B.tbl v, ty)

let rec default_value ty =
  match ty with
  | TUnit -> avalue (vunit (), Some ty, Span.default)
  | TBool -> avalue (vbool false, Some ty, Span.default)
  | TInt size ->
    avalue (vint (Integer.create ~value:0 ~size:size), Some ty, Span.default)
  | TRecord map -> avalue (vtuple (BatList.map default_value @@ RecordUtils.get_record_entries map),
                           Some ty, Span.default)
  | TTuple ts ->
    avalue (vtuple (BatList.map default_value ts), Some ty, Span.default)
  | TOption _ ->
    avalue (voption None, Some ty, Span.default)
  | TMap (ty1, ty2) ->
    avalue (vmap (create ~key_ty:ty1 (default_value ty2)), Some ty, Span.default)
  | TNode -> avalue (vnode 0, Some ty, Span.default)
  | TEdge -> avalue (vedge (0, 1), Some ty, Span.default)
  | TSubset (_, es) ->
    List.find_map (fun e -> match e.e with | EVal v -> Some v | _ -> None) es
  | TVar {contents= Link t} ->
    default_value t
  | TVar _ | QVar _ | TArrow _ ->
    failwith "internal error (default_value)"

let value_to_bdd (v: value) : Bdd.vt =
  let rec aux v idx =
    match v.v with
    | VUnit -> (* Encode unit as if it were a true boolean *)
      let var = B.ithvar idx in
      var, idx + 1
    | VBool b ->
      let var = B.ithvar idx in
      ((if b then var else Bdd.dnot var), idx + 1)
    | VInt i ->
      B.mk_int i idx, idx + Integer.size i
    | VTuple vs ->
      let base = Bdd.dtrue B.mgr in
      List.fold_left
        (fun (bdd_acc, idx) v ->
           let bdd, i = aux v idx in
           (Bdd.dand bdd_acc bdd, i) )
        (base, idx) vs
    | VRecord map ->
      (* Convert this to a tuple type, then encode that *)
      let tup = vtuple (RecordUtils.get_record_entries map) in
      aux tup idx
    | VNode n ->
      (* Encode same way as we encode ints *)
      aux (vint (Integer.create ~value:n ~size:32)) idx
    | VEdge (e1, e2) ->
      (* Encode same way as we encode tuples of nodes *)
      let tup = vtuple [vnode e1; vnode e2] in
      aux tup idx
    | VOption None ->
      let var = B.ithvar idx in
      let tag = Bdd.eq var (Bdd.dfalse B.mgr) in
      let dv = default_value (Nv_utils.OCamlUtils.oget v.vty) in
      let value, idx = aux dv (idx + 1) in
      (Bdd.dand tag value, idx)
    | VOption (Some dv) ->
      let var = B.ithvar idx in
      let tag = Bdd.eq var (Bdd.dtrue B.mgr) in
      let value, idx = aux dv (idx + 1) in
      (Bdd.dand tag value, idx)
    | VMap _ | VClosure _ ->
      failwith "internal error (value_to_bdd)"
  in
  let bdd, _ = aux v 0 in
  bdd

let vars_to_value vars ty =
  let open RecordUtils in
  let rec aux idx ty =
    let v, i =
      match get_inner_type ty with
      | TUnit -> vunit (), idx + 1 (* Same as a bool *)
      | TBool ->
        (vbool (B.tbool_to_bool vars.(idx)), idx + 1)
      | TInt size ->
        let acc = ref (Integer.create ~value:0 ~size:size) in
        for i = 0 to size-1 do
          let bit = B.tbool_to_bool vars.(idx + i) in
          if bit then
            let add = Integer.shift_left (Integer.create ~value:1 ~size:size) i in
            acc := Integer.add !acc add
        done ;
        (vint !acc, idx + size)
      | TTuple ts ->
        let vs, i =
          List.fold_left
            (fun (vs, idx) ty ->
               let v, i = aux idx ty in
               (v :: vs, i) )
            ([], idx) ts
        in
        (vtuple (List.rev vs), i)
      | TRecord map ->
        (* This will have been encoded as if it's a tuple.
           So get the tuple type and use that to decode *)
        let tup = TTuple (get_record_entries map) in
        aux idx tup
      | TNode ->
        (* Was encoded as int, so decode same way *)
        (match aux idx (TInt 32) with
         | {v = VInt n; _}, i ->  vnode (Integer.to_int n), i
         | _ -> failwith "impossible")
      | TEdge ->
        (* Was encoded as tuple of nodes *)
        (match aux idx (TTuple [TNode; TNode]) with
         | {v = VTuple [{v= VNode n1; _}; {v= VNode n2; _}]; _}, i -> vedge (n1, n2), i
         | _ -> failwith "impossible")
      | TOption tyo ->
        let tag = B.tbool_to_bool vars.(idx) in
        let v, i = aux (idx + 1) tyo in
        let v =
          if tag then voption (Some v)
          else voption None
        in
        (v, i)
      | TSubset (ty, _) ->
        aux idx ty
      | TArrow _ | TMap _ | TVar _ | QVar _ ->
        failwith "internal error (bdd_to_value)"
    in
    let ty =
      match ty with
      | TRecord map -> TTuple (get_record_entries map)
      | _ -> ty
    in
    (annotv ty v, i)
  in
  fst (aux 0 ty)

module ExpMap = BatMap.Make (struct
    type t = exp * value PSet.t

    let compare = Pervasives.compare
  end)

let map_cache = ref ExpMap.empty

let map ~op_key (f: value -> value) ((vdd, ty): t) : t =
  let cfg = Cmdline.get_cfg () in
  let g x = f (Mtbdd.get x) |> Mtbdd.unique B.tbl in
  if cfg.no_caching then (Mapleaf.mapleaf1 g vdd, ty)
  else
    let op =
      match ExpMap.Exceptionless.find op_key !map_cache with
      | None ->
        let o =
          User.make_op1 ~memo:(Memo.Cache (Cache.create1 ())) g
        in
        map_cache := ExpMap.add op_key o !map_cache ;
        o
      | Some op -> op
    in
      (User.apply_op1 op vdd, ty)

let pick_default_value (map,ty) =
  let count = ref (-1) in
  let value = ref None in
  Mtbdd.iter_cube
    (fun vars v ->
       let c = B.count_tops vars (B.ty_to_size ty) in
       if c > !count then count := c ;
       value := Some v )
    map ;
  Nv_utils.OCamlUtils.oget !value

let bindings ((map, ty): t) : (value * value) list * value =
  let bs = ref [] in
  let dv = pick_default_value (map, ty) in
  Mtbdd.iter_cube
    (fun vars v ->
       let lst = Array.to_list vars in
       let sz = B.ty_to_size ty in
       let expanded =
         if B.count_tops vars sz <= 5 then B.expand lst sz else [lst]
       in
       List.iter
         (fun vars ->
            if not (equal_values ~cmp_meta:false v dv) then
              let k = vars_to_value (Array.of_list vars) ty in
              bs := (k, v) :: !bs )
         expanded )
    map ;
  (!bs, dv)

let mapw_op_cache = ref ExpMap.empty

let map_when ~op_key (pred: bool Mtbdd.t) (f: value -> value)
    ((vdd, ty): t) : t =
  let cfg = Cmdline.get_cfg () in
  let g b v =
    if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique B.tbl
    else v
  in
  if cfg.no_caching then (Mapleaf.mapleaf2 g pred vdd, ty)
  else
    let op =
      match ExpMap.Exceptionless.find op_key !mapw_op_cache with
      | None ->
        let special =
          if cfg.no_cutoff then fun _ _ -> None
          else fun bdd1 bdd2 ->
            if Vdd.is_cst bdd1 && not (Mtbdd.get (Vdd.dval bdd1))
            then Some bdd2
            else None
        in
        let op =
          User.make_op2
            ~memo:(Memo.Cache (Cache.create2 ()))
            ~commutative:false ~idempotent:false ~special g
        in
        mapw_op_cache := ExpMap.add op_key op !mapw_op_cache ;
        op
      | Some op -> op
    in
    (User.apply_op2 op pred vdd, ty)

module MergeMap = BatMap.Make (struct
    type t =
      (exp * value PSet.t) * (value * value * value * value) option

    let compare = Pervasives.compare
  end)

let unwrap x =
  match x with
    | {v= VOption (Some v)} ->
      (true, v)
  | _ -> (false, vbool false)

let merge_op_cache = ref MergeMap.empty

let merge ?opt ~op_key (f: value -> value -> value) ((x, tyx): t)
    ((y, _): t) : t =
  let cfg = Cmdline.get_cfg () in
  let g x y =
    f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique B.tbl
  in
  if cfg.no_caching then (Mapleaf.mapleaf2 g x y, tyx)
  else
    let key = (op_key, opt) in
    let op =
      match MergeMap.Exceptionless.find key !merge_op_cache with
      | None ->
        let special =
          match (opt, cfg.no_cutoff) with
          | None, _ | _, true -> fun _ _ -> None
          | Some (el0, el1, er0, er1), false ->
            let bl0, vl0 = unwrap el0 in
            let bl1, vl1 = unwrap el1 in
            let br0, vr0 = unwrap er0 in
            let br1, vr1 = unwrap er1 in
            fun left right ->
              if
                bl0 && Vdd.is_cst left
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval left))
                  vl0
              then Some right
              else if
                bl1 && Vdd.is_cst left
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval left))
                  vl1
              then Some left
              else if
                br0 && Vdd.is_cst right
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval right))
                  vr0
              then Some left
              else if
                br1 && Vdd.is_cst right
                && equal_values ~cmp_meta:false
                  (Mtbdd.get (Vdd.dval right))
                  vr1
              then Some right
              else None
        in
        let o =
          User.make_op2
            ~memo:(Memo.Cache (Cache.create2 ()))
            ~commutative:false ~idempotent:false ~special g
        in
        merge_op_cache := MergeMap.add key o !merge_op_cache ;
        o
      | Some op -> op
    in
    (User.apply_op2 op x y, tyx)

let find ((map, _): t) (v: value) : value =
  let bdd = value_to_bdd v in
  let for_key = Mtbdd.constrain map bdd in
  Mtbdd.pick_leaf for_key

let update ((map, ty): t) (k: value) (v: value) : t =
  let leaf = Mtbdd.cst B.mgr B.tbl v in
  let key = value_to_bdd k in
  (Mtbdd.ite key leaf map, ty)

let from_bindings ~key_ty:ty
    ((bs, default): (value * value) list * value) : t =
  let map = create ~key_ty:ty default in
  List.fold_left (fun acc (k, v) -> update acc k v) map bs

let equal (bm1, _) (bm2, _) = Mtbdd.is_equal bm1 bm2
