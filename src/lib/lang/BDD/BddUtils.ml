open Syntax
open Cudd
open Syntax
open Nv_utils
open Nv_datastructures
open Batteries
open TotalMap
open TotalMap__Manager

module ValuesNV : Hashtbl.HashedType =
struct
  type t = value
  let hash = Syntax.hash_value ~hash_meta:false
  let equal = Syntax.equal_values ~cmp_meta:false
end

module BddNV = BddOverV(ValuesNV)

module type NVType =
sig
  val t : Syntax.ty
end

module FiniteNV(K:NVType) : FiniteType =
struct
  type key = value
  let key_ty = K.t
                 
  module B = BddNV
  open B

  let get_bit (n: Integer.t) (i: int) : bool =
    let z = Integer.value n in
    let marker = (Z.shift_left Z.one i) in
    Z.logand z marker <> Z.zero

  let mk_int i idx =
    let acc = ref (Bdd.dtrue mgr) in
    let sz = Integer.size i in
    for j = 0 to sz - 1 do
      let var = ithvar (idx + j) in
      let bit = get_bit i j in
      let bdd = if bit then Bdd.dtrue mgr else Bdd.dfalse mgr in
      acc := Bdd.dand !acc (Bdd.eq var bdd)
    done ;
    !acc

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
  | TVar {contents= Link t} ->
    default_value t
  | TVar _ | QVar _ | TArrow _ ->
    failwith "internal error (default_value)"

  let key_to_bdd (v: value) : Bdd.vt =
    let rec aux v idx =
      match v.v with
      | VUnit -> (* Encode unit as if it were a true boolean *)
        let var = B.ithvar idx in
        var, idx + 1
      | VBool b ->
        let var = B.ithvar idx in
        ((if b then var else Bdd.dnot var), idx + 1)
      | VInt i ->
        mk_int i idx, idx + Integer.size i
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

  let bdd_to_key vars =
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
          (match aux idx (TInt tnode_sz) with
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
    fst (aux 0 key_ty)

  let rec ty_to_size ty =
    match get_inner_type ty with
    | TUnit -> 1 (* I don't understand how Cudd BDDs work, so encode TUnit as false *)
    | TBool -> 1
    | TInt n -> n
    | TOption tyo -> 1 + ty_to_size tyo
    | TTuple ts ->
      List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
    | TRecord tmap -> ty_to_size (TTuple (RecordUtils.get_record_entries tmap))
    | TNode -> ty_to_size (TInt tnode_sz) (* Encode as int *)
    | TEdge -> ty_to_size (TTuple [TNode; TNode]) (* Encode as node pair *)
    | TArrow _ | TMap _ | TVar _ | QVar _ ->
      failwith ("internal error (ty_to_size): " ^ (PrintingRaw.show_ty ty))

  let key_size = ty_to_size key
end
