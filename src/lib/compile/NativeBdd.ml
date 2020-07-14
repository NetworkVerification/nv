open Cudd
open Nv_lang
open Syntax
open Nv_datastructures
open Batteries
open Embeddings
open CompileBDDs
open Collections
open Nv_utils

module B = BddUtilsNat

(* value_to_bdd converts an OCaml Value to a Bdd. It requires an NV type for the given OCaml value *)
let value_to_bdd (record_fns: (int*int) -> 'a -> 'b) (typ : Syntax.ty) (v: 'v) : Bdd.vt =
  let rec aux typ v idx =
    match typ with
    | TUnit -> (* Encode unit as if it were a true boolean - this should be a constant true *)
      Cudd.Bdd.dtrue B.mgr, idx 
    | TBool ->
      let var = B.ithvar idx in
      ((if (Obj.magic v) then var else Bdd.dnot var), idx + 1)
    | TInt sz ->
      B.mk_int sz (Obj.magic v) idx, idx + sz
    | TTuple ts ->
      let base = Bdd.dtrue B.mgr in
      let n = BatList.length ts in
      let proj_fun i = (i, n) in
      let proj_val i = record_fns (proj_fun i) in
      List.fold_lefti
        (fun (bdd_acc, idx) vindex ty ->
           let bdd, i = aux ty (Obj.magic (proj_val vindex v)) idx in
           (Bdd.dand bdd_acc bdd, i) )
        (base, idx) ts
    | TNode ->
      (* Encode same way as we encode ints *)
      B.mk_int tnode_sz (Obj.magic v) idx, idx + tnode_sz
    | TEdge ->
      let bdd1, i = aux TNode (fst (Obj.magic v)) idx in
      let bdd2, i = aux TNode (snd (Obj.magic v)) i in
        (Bdd.dand bdd1 bdd2, i)
    | TOption typ ->
      (match Obj.magic v with
        | None ->
          let var = B.ithvar idx in
          let tag = Bdd.eq var (Bdd.dfalse B.mgr) in
          let dv = BddMap.default_value (Nv_utils.OCamlUtils.oget v.vty) in
          let value, idx = aux typ dv (idx + 1) in
            (Bdd.dand tag value, idx)
        | Some v ->
          let var = B.ithvar idx in
          let tag = Bdd.eq var (Bdd.dtrue B.mgr) in
          let value, idx = aux typ v (idx + 1) in
            (Bdd.dand tag value, idx)
      )
    | TMap _ | TVar _ | QVar _ | TArrow _ | TRecord _->
      failwith "internal error (value_to_bdd)"
  in
  let bdd, _ = aux typ v 0 in
  bdd

(* Used to cache functions and their closures *)
module HashClosureMap = BatMap.Make (struct
    type t = int * unit (*NOTE: unit here is a placeholder for the closure type which is a tuple of OCaml variables*)
    let compare = Pervasives.compare
  end)

let map_cache = Obj.magic (ref HashClosureMap.empty)

(* Takes as input the id of the key type, allocates sufficient decision nodes in the BDD, and creates a MTBDD with an OCaml value as leaf*)
let create ~(key_ty_id:int) ~(val_ty_id:int) (vnat: 'v) : 'v t =
  let key_ty = TypeIds.get_elt type_store key_ty_id in
    B.set_size (B.ty_to_size key_ty);
    {bdd = Mtbdd.cst B.mgr B.tbl vnat;
     key_ty_id=key_ty_id;
     val_ty_id=val_ty_id}
     

(* (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b) *)
(** Takes the function of record_constructors and record_projections, [op_key] a
   tuple of the hashconsed NV expression and a tuple of OCaml variables
   (strings) that represent the closure of the mapped expression, the new type
   of the map, the function mapped and the map. *)
let map (op_key: (int * 'f)) (vty_new_id: int) (f: 'a1 -> 'a2) (vmap: 'a1 t) : 'a2 t =
  let vdd = vmap.bdd in
  let g x = f (Mtbdd.get x) |> Mtbdd.unique B.tbl in
  let op =
    match HashClosureMap.Exceptionless.find op_key !map_cache with
    | None ->
      let o = User.make_op1 ~memo:(Cudd.Memo.Global) g
      in
      map_cache := HashClosureMap.add op_key o !map_cache ;
      o
    | Some op -> op
  in
  {bdd = User.apply_op1 op vdd; key_ty_id = vmap.key_ty_id; val_ty_id = vty_new_id}


(** Takes as input an OCaml map and an ocaml key and returns an ocaml value*)
let find record_fns (vmap: 'v t) (k: 'key) : 'v =
  let key_ty = TypeIds.get_elt type_store vmap.key_ty_id in
  let bdd = value_to_bdd record_fns key_ty k in
  let for_key = Mtbdd.constrain vmap.bdd bdd in
    Mtbdd.pick_leaf for_key

let update record_fns (vmap: 'v t) (k: 'key) (v: 'v): 'v t =
  let key_ty = TypeIds.get_elt type_store vmap.key_ty_id in
  let key = value_to_bdd record_fns key_ty k in
  let leaf = Mtbdd.cst B.mgr B.tbl v in
    {vmap with bdd = Mtbdd.ite key leaf vmap.bdd}

module HashMergeMap = BatMap.Make (struct
    type t =
      (int * unit) * (unit * unit * unit * unit) option

    let compare = Pervasives.compare
  end)

let merge_op_cache = ref HashMergeMap.empty

let unwrap (x: 'a) : bool * 'b =
  match Obj.magic x with
    | Some v ->
      (true, Obj.magic v)
    | _ ->
      (false, false)

(* NOTE: Currently vty1=vty2 and the type of the result is also vty1*)
(** [op_key] is a tuple of the id of the function used to perform the
   merge and a tuple that contains the values of the closure.*)
   let merge ?(opt=None) (op_key: (int * 'f)) f (vmap1: 'a t) (vmap2: 'a t) =
   let cfg = Cmdline.get_cfg () in
   let g x y =
     f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique B.tbl
   in
   (* if cfg.no_caching then
    *   {vmap1 with bdd = (Mapleaf.mapleaf2 g (fst vmap1.bdd) (fst vmap2.bdd), (snd vmap1.bdd))}
    *   else *)
   let key = (Obj.magic op_key, opt) in
   let op =
     match HashMergeMap.Exceptionless.find key !merge_op_cache with
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
                     && (Mtbdd.get (Vdd.dval left) = vl0)
                   then Some right
                   else if
                     bl1 && Vdd.is_cst left
                     && (Mtbdd.get (Vdd.dval left) = vl1)
                   then Some left
                   else if
                     br0 && Vdd.is_cst right
                     && (Mtbdd.get (Vdd.dval right) = vr0)
                   then Some left
                   else if
                     br1 && Vdd.is_cst right
                     && (Mtbdd.get (Vdd.dval right) = vr1)
                   then Some right
                   else None
         in
         let o =
           User.make_op2 ~memo:(Cudd.Memo.Global)
             ~commutative:false ~idempotent:false ~special g
         in
           merge_op_cache := HashMergeMap.add key o !merge_op_cache ;
           o
       | Some op -> op
   in
     {vmap1 with bdd = User.apply_op2 op vmap1.bdd vmap2.bdd}

let equal m1 m2 = Mtbdd.is_equal m1.bdd m2.bdd

(** * MapIf related functions*)
let mapw_op_cache = Obj.magic (ref HashClosureMap.empty)

let mapw_pred_cache = ref HashClosureMap.empty

(* Given the argument [x], the corrresponding bdd [bddf], a predicate's body [f] and a closure (tuple of values) [clos] returns
 * an environment of NV values that can be used to build the BDD. *)
let build_env (x : Syntax.var) (bddf: BddFuncNat.t) (f: exp) (clos: 'a) =
  let freeVars = Syntax.free (BatSet.PSet.singleton ~cmp:Var.compare x) f in
  let freeList = BatSet.PSet.to_list freeVars in
  let rec loop list clos acc =
    match list with
    | [] -> acc
    | [y] ->
      Env.update acc y (BddFuncNat.eval_value (embed_value_id (snd clos) (fst clos)))
    | y :: ys ->
      let elt = Obj.magic (fst clos) in
      let clos = snd clos in
      let env = Env.update acc y (BddFuncNat.eval_value (embed_value_id (snd elt) (fst elt))) in
      loop ys (Obj.magic clos) env
  in
  loop freeList (Obj.magic clos) (Env.bind x bddf)

let mapIf (pred_key: int * 'g) (op_key : int * 'f) (vty_new_id: int) (f: 'a1 -> 'a2) (vmap : 'a1 t) : 'a2 t =
  let cfg = Cmdline.get_cfg () in
  let g b v =
    if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique B.tbl
    else v
  in
  let pred =
    match HashClosureMap.Exceptionless.find pred_key !mapw_pred_cache with
    | None ->
      (* Printf.printf "edge: %d,%d\n" (fst (fst (Obj.magic clos))) (snd (fst (Obj.magic clos))); *)
      let pred = Collections.ExpIds.get_elt pred_store (fst pred_key) in
      let predFun =
        match pred.e with
        | EFun predFun -> predFun
        | _ -> failwith "expected a function"
      in
      (* Create a BDD that corresponds to all keys of type argty*)
      let bddf = BddFuncNat.create_value (OCamlUtils.oget predFun.argty) in
      (* Build the closure environment of the predicate *)
      let env = build_env predFun.arg bddf predFun.body (snd pred_key) in
      (* Build the BDD that captures the predicate's semantics *)
      let bddf = BddFuncNat.eval env predFun.body in
      (* If it's a value, create a BDD *)
      let bddf = match bddf with
        | Value v -> BddFuncNat.eval_value v
        | _ -> bddf
      in
      (match bddf with
       | BBool bdd ->
         let mtbdd = BddFuncNat.wrap_mtbdd bdd in
         mapw_pred_cache :=
           HashClosureMap.add pred_key mtbdd !mapw_pred_cache ;
         mtbdd
       | BMap mtbdd ->
         let mtbdd = (BddFuncNat.value_mtbdd_bool_mtbdd (fst mtbdd)) in
         mapw_pred_cache  := HashClosureMap.add pred_key mtbdd !mapw_pred_cache ;
         mtbdd
       | _ -> failwith "A boolean bdd was expected but something went wrong")
    | Some mtbdd -> (*cache hit *)
      mtbdd
  in

  let op =
    match HashClosureMap.Exceptionless.find op_key !mapw_op_cache with
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
          ~memo:(Cudd.Memo.Global)
          ~commutative:false ~idempotent:false ~special g
      in
      mapw_op_cache := HashClosureMap.add op_key op !mapw_op_cache ;
      op
    | Some op -> op
  in
  {vmap with bdd = User.apply_op2 op pred vmap.bdd;
             val_ty_id = vty_new_id}


(* Cache for map forall operations *)
let forall_op_cache = Obj.magic (ref HashClosureMap.empty)

let forall (pred_key: int * 'g) (op_key : int * 'f) (vty_new_id: int) (f: 'a1 -> 'a2) (vmap : 'a t) : bool =
  let cfg = Cmdline.get_cfg () in
  let g b v =
    if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique B.tbl
    else (Obj.magic true) |> Mtbdd.unique B.tbl
  in

  let pred =
    match HashClosureMap.Exceptionless.find pred_key !mapw_pred_cache with
    | None ->
      (* Printf.printf "edge: %d,%d\n" (fst (fst (Obj.magic clos))) (snd (fst (Obj.magic clos))); *)
      let pred = Collections.ExpIds.get_elt pred_store(fst pred_key) in
      let predFun =
        match pred.e with
        | EFun predFun -> predFun
        | _ -> failwith "expected a function"
      in
      (* Create a BDD that corresponds to all keys of type argty*)
      let bddf = BddFuncNat.create_value (OCamlUtils.oget predFun.argty) in
      (* Build the closure environment of the predicate *)
      let env = build_env predFun.arg bddf predFun.body (snd pred_key) in
      (* Build the BDD that captures the predicate's semantics *)
      let bddf = BddFuncNat.eval env predFun.body in
      (match bddf with
       | BBool bdd ->
         let mtbdd = BddFuncNat.wrap_mtbdd bdd in
         mapw_pred_cache :=
           HashClosureMap.add pred_key mtbdd !mapw_pred_cache ;
         mtbdd
       | BMap mtbdd ->
         let mtbdd = (BddFuncNat.value_mtbdd_bool_mtbdd (fst mtbdd)) in
         mapw_pred_cache  := HashClosureMap.add pred_key mtbdd !mapw_pred_cache ;
         mtbdd
       | _ -> failwith "A boolean bdd was expected but something went wrong")
    | Some mtbdd -> (*cache hit *)
      mtbdd
  in

    let op =
      match HashClosureMap.Exceptionless.find op_key !forall_op_cache with
      | None ->
        let special = fun bdd1 _ ->
            if Vdd.is_cst bdd1 && not (Mtbdd.get (Vdd.dval bdd1))
            then Some (Mtbdd.cst B.mgr B.tbl (Obj.magic true))
            else None
        in
        let op =
          User.make_op2
            ~memo:(Cudd.Memo.Global)
            ~commutative:false ~idempotent:false ~special g
        in
        forall_op_cache := HashClosureMap.add op_key op !forall_op_cache ;
        op
      | Some op ->
        op
    in
    let op_result = User.apply_op2 op pred vmap.bdd in
    Array.fold_left (fun acc v -> Obj.magic (v && acc)) true
      (Mtbdd.leaves op_result)