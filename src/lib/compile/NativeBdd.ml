open Cudd
open Nv_lang
open Syntax
open Nv_datastructures
open Batteries
open BddMap
open Embeddings
open CompileBDDs
open Collections
open Nv_utils

module B = BddUtils


(* should I start by trying BatMap? would also set a comparison basis*)
  (* mcreate v : embed value return map.
     mget k m: embed key, get from the map, unembed value.
     mset k v m: embed key, value and set them on the map.
     mmap f m: for every value, unembed it, apply the function f and then embed the result.
     merge: unembed both values, apply f, embed result.
     mapIf p f m: create BDD for predicate p during compilation.
  *)

(* Used to cache functions and their closures *)
module HashClosureMap = BatMap.Make (struct
    type t = int * unit (*NOTE: unit here is a placeholder for the closure type which is a tuple of OCaml variables*)
    let compare = Pervasives.compare
  end)

let map_cache = ref HashClosureMap.empty

let create ~(key_ty_id:int) ~(val_ty_id:int) (vnat: 'v) : t =
  let key_ty = get_type key_ty_id in
  let v = embed_value_id val_ty_id vnat in
  {bdd = BddMap.create key_ty v; key_ty_id=key_ty_id; val_ty_id=val_ty_id}


(* (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b) *)
(** Takes the function of record_constructors and record_projections, [op_key] a
   tuple of the hashconsed NV expression and a tuple of OCaml variables
   (strings) that represent the closure of the mapped expression, the new type
   of the map, the function mapped and the map. *)
let map (op_key: (int * 'f)) (vty_new_id: int) (f: 'a1 -> 'a2) (vmap: t) : t =
  let vdd = fst (vmap.bdd) in
  let kty = snd (vmap.bdd) in
  let vty_old_id = vmap.val_ty_id in
  (* let cfg = Cmdline.get_cfg () in *)
  let f_embed =
    fun x -> (f (unembed_value_id vty_old_id x))
             |> embed_value_id vty_old_id (*NOTE: changed this from vty_new_id*)
  in
  (* let f_embed =
   *   fun x -> (f (unembed_value record_cnstrs record_fns (get_type vty_old_id) x))
   *            |> embed_value record_fns (get_type vty_old_id) (\*NOTE: changed this from vty_new_id*\)
   * in *)
  let g x = f_embed (Mtbdd.get x) |> Mtbdd.unique B.tbl in
  (* if cfg.no_caching then
   *   {bdd = (Mapleaf.mapleaf1 g vdd, kty); key_ty_id = vmap.key_ty_id; val_ty_id = vty_new_id}
   *   else *)
  let op =
    match HashClosureMap.Exceptionless.find op_key !map_cache with
    | None ->
      let o =
        User.make_op1 ~memo:(Memo.Cache (Cudd.Cache.create1 ())) g
      in
      map_cache := HashClosureMap.add op_key o !map_cache ;
      o
    | Some op -> op
  in
  {bdd = (User.apply_op1 op vdd, kty); key_ty_id = vmap.key_ty_id; val_ty_id = vty_new_id}


(** Takes as input an OCaml map and an ocaml key and returns an ocaml value*)
let find _ (vmap: t) (k: 'key) : 'v =
  let k_embed = embed_value_id vmap.key_ty_id k in
  let value = BddMap.find vmap.bdd k_embed in
  unembed_value_id vmap.val_ty_id value


let update vty (vmap: t) (k: 'key) (v: 'v): t =
  let k_embed = embed_value_id vmap.key_ty_id (Obj.magic k) in
  let v_embed = embed_value_id vty (Obj.magic v) in
  (* let k_embed = embed_value record_fns (get_type vmap.key_ty_id) (Obj.magic k) in
   * let v_embed = embed_value record_fns (get_type vty) (Obj.magic v) in *)
    {vmap with bdd = BddMap.update vmap.bdd k_embed v_embed}


module HashMergeMap = BatMap.Make (struct
    type t =
      (int * unit) * (unit * unit * unit * unit) option

    let compare = Pervasives.compare
  end)

let merge_op_cache = ref HashMergeMap.empty

let unwrap vty_id (x: 'a) : bool * 'b =
  match Obj.magic x with
    | Some v ->
      (true, embed_value_id vty_id v)
    | _ ->
      (false, vbool false)

(* NOTE: Currently vty1=vty2 and the type of the result is also vty1*)
(** [op_key] is a tuple of the id of the function used to perform the
   merge and a tuple that contains the values of the closure.*)
let merge ?(opt=None) (op_key: (int * 'f)) f (vmap1: t) (vmap2: t) = (* (((m1, kty), vty1):t) (((m2,_), _):t) *)
  let cfg = Cmdline.get_cfg () in
  let f_embed =
    fun x y ->
      let xnat = unembed_value_id vmap1.val_ty_id x in
      let ynat = unembed_value_id vmap2.val_ty_id y in
      embed_value_id vmap1.val_ty_id (f xnat ynat)
  in
  let g x y =
    f_embed (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique B.tbl
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
                  let vty1_id = vmap1.val_ty_id in
                  let bl0, vl0 = unwrap vty1_id el0 in
                  let bl1, vl1 = unwrap vty1_id el1 in
                  let br0, vr0 = unwrap vty1_id er0 in
                  let br1, vr1 = unwrap vty1_id er1 in
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
              User.make_op2 ~memo:(Memo.Cache (Cudd.Cache.create2 ()))
                ~commutative:false ~idempotent:false ~special g
            in
              merge_op_cache := HashMergeMap.add key o !merge_op_cache ;
              o
          | Some op -> op
  in
  {vmap1 with bdd = (User.apply_op2 op (fst vmap1.bdd) (fst vmap2.bdd), (snd vmap1.bdd))}

let equal m1 m2 = BddMap.equal m1.bdd m2.bdd

(** * MapIf related functions*)
let mapw_op_cache = ref HashClosureMap.empty

let mapw_pred_cache = ref HashClosureMap.empty

(* Given the argument [x], the corrresponding bdd [bddf], a predicate's body [f] and a closure (tuple of values) [clos] returns
 * an environment to build the BDD. *)
let build_env (x : Syntax.var) (bddf: BddFunc.t) (f: exp) (clos: 'a) =
  let freeVars = Syntax.free (BatSet.PSet.singleton ~cmp:Var.compare x) f in
  let freeList = BatSet.PSet.to_list freeVars in
  let rec loop list clos acc =
    match list with
    | [] -> acc
    | [y] ->
      Env.update acc y (BddFunc.eval_value (embed_value_id (snd clos) (fst clos)))
    | y :: ys ->
      let elt = Obj.magic (fst clos) in
      let clos = snd clos in
      let env = Env.update acc y (BddFunc.eval_value (embed_value_id (snd elt) (fst elt))) in
      loop ys (Obj.magic clos) env
  in
  loop freeList (Obj.magic clos) (Env.bind x bddf)

let mapIf (pred_key: int * 'g) (op_key : int * 'f) (vty_new_id: int) (f: 'a1 -> 'a2) (vmap : t) : t =
  let cfg = Cmdline.get_cfg () in
  let f_embed =
    fun x -> (f (unembed_value_id vmap.val_ty_id x))
             |> embed_value_id vty_new_id
  in
  let g b v =
    if Mtbdd.get b then f_embed (Mtbdd.get v) |> Mtbdd.unique B.tbl
    else v
  in

  let pred =
    match HashClosureMap.Exceptionless.find pred_key !mapw_pred_cache with
    | None ->
      (* Printf.printf "edge: %d,%d\n" (fst (fst (Obj.magic clos))) (snd (fst (Obj.magic clos))); *)
      let pred = get_pred (fst pred_key) in
      let predFun =
        match pred.e with
        | EFun predFun -> predFun
        | _ -> failwith "expected a function"
      in
      let bddf = BddFunc.create_value (OCamlUtils.oget predFun.argty) in
      let env = build_env predFun.arg bddf predFun.body (snd pred_key) in
      let bddf = BddFunc.eval env predFun.body in
      (match bddf with
       | BBool bdd ->
         let mtbdd = BddFunc.wrap_mtbdd bdd in
         mapw_pred_cache :=
           HashClosureMap.add pred_key mtbdd !mapw_pred_cache ;
         mtbdd
       | _ -> failwith "A boolean bdd was expected but something went wrong")
    | Some mtbdd ->
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
          ~memo:(Memo.Cache (Cudd.Cache.create2 ()))
          ~commutative:false ~idempotent:false ~special g
      in
      mapw_op_cache := HashClosureMap.add op_key op !mapw_op_cache ;
      op
    | Some op -> op
  in
  {vmap with bdd = (User.apply_op2 op pred (fst vmap.bdd), snd vmap.bdd);
             val_ty_id = vty_new_id}
