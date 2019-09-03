open Cudd
open Nv_lang
open Syntax
open Nv_datastructures
open Batteries
open BddMap
open Embeddings

module B = BddUtils

(* should I start by trying BatMap? would also set a comparison basis*)
  (* mcreate v : embed value return map.
     mget k m: embed key, get from the map, unembed value.
     mset k v m: embed key, value and set them on the map.
     mmap f m: for every value, unembed it, apply the function f and then embed the result.
     merge: unembed both values, apply f, embed result.
     mapIf p f m: need to somehow create BDD out of ocaml function..

It seems as if only mapIf would require us to also embed/unembed expressions not just values
need an ocaml lift function (taking you to bdds) on ocaml functions:


let bddf = BddFunc.create_value f.argty in
match (lift p bddf)
|...

lift (p : exp) =
  match p with
  | EVar x -> Var.name x
  | EVal v -> probably easy?
  | And e1,e2 -> Band (lift e1) (lift e2)

  *)

(* BddMap plus the type of the values*)
type t = BddMap.t * Syntax.ty

module HashClosureMap = BatMap.Make (struct
    type t = int * unit (*NOTE: unit here is a placeholder for the closure type*)
    let compare = Pervasives.compare
  end)

let map_cache = ref HashClosureMap.empty

let create (record_fns: string -> 'a -> 'b) ~key_ty ~val_ty (vnat: 'v) : t =
  let v = embed_value record_fns val_ty vnat in
    (BddMap.create key_ty v, val_ty)

(*TODO: deal with caching, we probably need to explicitly capture the closure,
   so when translating a map operation, we might wanted to represent it as "map
   (free_vars list) exp f m" where exp is the original NV expression or perhaps
   just an integer to represent it. Why make cache checking more expensive than
   it should be? And (free_vars list)*)
let map (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b)
    (op_key: (int * 'f)) (vty_new: Syntax.ty) (f: 'a1 -> 'a2) (((vdd, kty), vty_old): t) : t =
  let cfg = Cmdline.get_cfg () in
  let f_embed =
    fun x -> (f (unembed_value record_cnstrs record_fns vty_old x))
             |> embed_value record_fns vty_new
  in
  let g x = f_embed (Mtbdd.get x) |> Mtbdd.unique B.tbl in
    if cfg.no_caching then
      ((Mapleaf.mapleaf1 g vdd, kty), vty_new)
    else
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
        ((User.apply_op1 op vdd, kty), vty_new)

(*TODO: implement caching *)

(** Takes as input an OCaml map and an ocaml key and returns an ocaml value*)
let find (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b)
    (((map,kty), vty): t) (k: 'key) : 'v =
  let k_embed = embed_value record_fns kty k in
    BddMap.find (map,kty) k_embed
    |> unembed_value record_cnstrs record_fns vty

let update (record_fns: string -> 'a -> 'b) (((vdd,kty),vty): t) (k: 'key) (v: 'v): t =
  let k_embed = embed_value record_fns kty (Obj.magic k) in
  let v_embed = embed_value record_fns vty (Obj.magic v) in
    (BddMap.update (vdd,kty) k_embed v_embed, vty)


module HashMergeMap = BatMap.Make (struct
    type t =
      (int * unit) * (unit * unit * unit * unit) option

    let compare = Pervasives.compare
  end)

let merge_op_cache = ref HashMergeMap.empty

let unwrap record_fns vty (x: 'a) : bool * 'b =
  match Obj.magic x with
    | Some v ->
      (true, embed_value record_fns vty v)
    | _ ->
      (false, vbool false)

(* NOTE: Currently vty1=vty2 and the type of the result is also vty1*)
(** [op_key] is a tuple of the hashcons of the function used to perform the
   merge and a tuple that contains the values of the closure.*)
let merge (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b)
    ?(opt=None) (op_key: (int * 'f)) f (((m1, kty), vty1):t) (((m2,_), _):t) =
  let cfg = Cmdline.get_cfg () in
  let f_embed =
    fun x y ->
      let xnat = unembed_value record_cnstrs record_fns vty1 x in
      let ynat = unembed_value record_cnstrs record_fns vty1 y in
      embed_value record_fns vty1 (f xnat ynat)
  in
  let g x y =
    f_embed (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique B.tbl
  in
    if cfg.no_caching then
      ((Mapleaf.mapleaf2 g m1 m2, kty), vty1)
    else
      let key = (Obj.magic op_key, opt) in
      let op =
        match HashMergeMap.Exceptionless.find key !merge_op_cache with
          | None ->
            let special =
              match (opt, cfg.no_cutoff) with
                | None, _ | _, true -> fun _ _ -> None
                | Some (el0, el1, er0, er1), false ->
                  let bl0, vl0 = unwrap record_fns vty1 el0 in
                  let bl1, vl1 = unwrap record_fns vty1 el1 in
                  let br0, vr0 = unwrap record_fns vty1 er0 in
                  let br1, vr1 = unwrap record_fns vty1 er1 in
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
        ((User.apply_op2 op m1 m2, kty), vty1)

let equal (bm1, _) (bm2, _) = BddMap.equal bm1 bm2

(*TODO: mapIf...*)
