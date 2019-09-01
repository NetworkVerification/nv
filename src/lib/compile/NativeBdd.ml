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

let create (record_fns: string -> 'a -> 'b) ~key_ty ~val_ty (vnat: 'a) : t =
  let v = embed_value record_fns val_ty vnat in
    (BddMap.create key_ty v, val_ty)

(*TODO: deal with caching, we probably need to explicitly capture the closure,
   so when translating a map operation, we might wanted to represent it as "map
   (free_vars list) exp f m" where exp is the original NV expression or perhaps
   just an integer to represent it. Why make cache checking more expensive than
   it should be? And (free_vars list)*)
let map (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b)
    (vty_new: Syntax.ty) (f: 'a -> 'b) (((vdd, kty), vty_old): t) : t =
  let cfg = Cmdline.get_cfg () in
  let f_embed =
    fun x -> unembed_value record_cnstrs record_fns vty_old x
             |> f |> embed_value record_fns vty_new
  in
  let g x = f_embed (Mtbdd.get x) |> Mtbdd.unique B.tbl in
    ((Mapleaf.mapleaf1 g vdd, kty), vty_new)
(*TODO: implement caching *)


let find (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b)
    (((map,kty), vty): t) (k: 'b) : 'a =
  let k_embed = embed_value record_fns kty k in
    BddMap.find (map,kty) k_embed
    |> unembed_value record_cnstrs record_fns vty

let update (record_fns: string -> 'a -> 'b) (((vdd,kty),vty): t) (k: 'a) (v: 'b): t =
  let k_embed = embed_value record_fns kty k in
  let v_embed = embed_value record_fns vty v in
    (BddMap.update (vdd,kty) k_embed v_embed, vty)

(* NOTE: Currently vty1=vty2 and the type of the result is also vty1*)
(*TODO: implement caching*)
let merge (record_cnstrs: string -> 'c) (record_fns: string -> 'a -> 'b)
    f (((m1, kty), vty1):t) (((m2,_), _):t) =
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
    ((Mapleaf.mapleaf2 g m1 m2, kty), vty1)

let equal (bm1, _) (bm2, _) = BddMap.equal bm1 bm2

(*TODO: mapIf...*)
