(*
open Cudd
open Syntax
open Nv_datastructures
open Batteries

module B = BddUtils

(* should I start by trying BatMap? would also set a comparison basis*)
  (* mcreate v : embed value return map.
     mget k m: embed key, get from the map, unembed value.
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



module type BddUtilsNatSig =
sig
  type valueNat
  val hash: valueNat -> int
  val equal: valueNat -> valueNat -> bool
end

module BddMapNat(BddUtilsNat:BddUtilsNatSig) =
struct
  open BddUtilsNat
  type t = valueNat Mtbdd.t

  let tbl = Mtbdd.make_table ~hash:hash ~equal:equal

  let create ~key_ty (v: valueNat) : t =
    B.set_size (B.ty_to_size key_ty);
    Mtbdd.cst B.mgr tbl v

  let rec default_value ty =
    match ty with
        | TUnit -> Obj.magic ()
        | TBool -> Obj.magic false
        | TInt size ->
          Obj.magic (Integer.create ~value:0 ~size:size)
        | TRecord map ->
          failwith "Later"
        | TTuple ts ->
          failwith "Later"
        | TOption _ ->
          Obj.magic None
        | TMap (ty1, ty2) ->
          Obj.magic (create ~key_ty:ty1 (default_value ty2))
        | TVar {contents= Link t} ->
          default_value t
        | TNode | TEdge -> failwith "later"
        | TVar _ | QVar _ | TArrow _ ->
          failwith "internal error (default_value)"

let value_to_bdd ty (v: 'a) : Bdd.vt =
  let rec aux v idx =
    match ty with
    | TBool ->
      let var = B.ithvar idx in
        ((if (Obj.magic v) then var else Bdd.dnot var), idx + 1)
    | TInt i ->
      B.mk_int (Obj.magic v) idx, idx + i
    | TOption _ ->
      (match Obj.magic v with
        | None ->
          let var = B.ithvar idx in
          let tag = Bdd.eq var (Bdd.dfalse B.mgr) in
          let dv = default_value ty in
          let value, idx = aux dv (idx + 1) in
            (Bdd.dand tag value, idx)
        | Some dv ->
          let var = B.ithvar idx in
          let tag = Bdd.eq var (Bdd.dtrue B.mgr) in
          let value, idx = aux dv (idx + 1) in
            (Bdd.dand tag value, idx))
    | _ ->
      failwith "internal error (value_to_bdd)"
  in
  let bdd, _ = aux v 0 in
    bdd

let vars_to_value vars ty : 'a =
  let rec aux idx ty =
    match get_inner_type ty with
      | TBool ->
        (Obj.magic (B.tbool_to_bool vars.(idx)), idx + 1)
      | TInt size ->
        let acc = ref (Integer.create ~value:0 ~size:size) in
          for i = 0 to size-1 do
            let bit = B.tbool_to_bool vars.(idx + i) in
              if bit then
                let add = Integer.shift_left (Integer.create ~value:1 ~size:size) i in
                  acc := Integer.add !acc add
          done ;
          (Obj.magic !acc, idx + size)
      | TOption tyo ->
        let tag = B.tbool_to_bool vars.(idx) in
        let v, i = aux (idx + 1) tyo in
        let v = if tag then (Some v) else None in
          (Obj.magic v, i)
      | TArrow _ | TMap _ | TVar _ | QVar _ ->
        failwith "internal error (bdd_to_value)"
  in
    fst (aux 0 ty)

(*TODO: deal with caching*)
let map (f: 'a -> 'b) (map: t) : 'b t =
  let g x = f (Mtbdd.get x) |> Mtbdd.unique B.tbl in
    Mapleaf.mapleaf1 g map

let pick_default_value (map : 'a t) ty : 'a =
  let count = ref (-1) in
  let value = ref None in
    Mtbdd.iter_cube
      (fun vars v ->
         let c = B.count_tops vars (B.ty_to_size ty) in
           if c > !count then count := c ;
           value := Some v )
      map;
    Nv_utils.OCamlUtils.oget !value

let bindings (map: 'b t) ty : ('a * 'b) list * 'b =
  let bs = ref [] in
  let dv = pick_default_value map ty in
  Mtbdd.iter_cube
    (fun vars v ->
       let lst = Array.to_list vars in
       let sz = B.ty_to_size ty in
       let expanded =
         if B.count_tops vars sz <= 5 then B.expand lst sz else [lst]
       in
       List.iter
         (fun vars ->
            if not (v = dv) then (* TODO: may need to specialize equality*)
              let k = vars_to_value (Array.of_list vars) ty in
              bs := (k, v) :: !bs )
         expanded )
    map ;
  (!bs, dv)

(*TODO: more functions here...*)

let find (map: 'a t) key_ty (k: 'b) : 'a =
  let bdd = value_to_bdd key_ty k in
  let for_key = Mtbdd.constrain map bdd in
  Mtbdd.pick_leaf for_key

let update (map: 'b t) key_ty (k: 'a) (v: 'b) : 'b t =
  let leaf = Mtbdd.cst B.mgr B.tbl v in
  let key = value_to_bdd key_ty k in
  Mtbdd.ite key leaf map

end
*)
