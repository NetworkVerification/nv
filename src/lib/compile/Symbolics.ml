open Nv_lang
open Nv_utils
open Nv_datastructures
open Syntax
open BddMap
open Embeddings
open CompileBDDs

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
    let _ = get_fresh_type_id ty1 in
    let _ = get_fresh_type_id ty2 in
    avalue (vmap (create ~key_ty:ty1 (default_value ty2)), Some ty, Span.default)
  | TNode -> avalue (vnode 0, Some ty, Span.default)
  | TEdge -> avalue (vedge (0, 1), Some ty, Span.default)
  | TVar {contents= Link t} ->
    default_value t
  | TSubset (_, es) -> List.hd es |> Syntax.exp_to_value
  | TVar _ | QVar _ | TArrow _ ->
    failwith "internal error (default_value)"

(** A module to hold values of symbolic variables*)
module type PackedSymbolics =
sig
  (* returns the value of the ith symbolic variable, takes the record constructors and projcetors*)
  val get_symb : (string -> 'c) -> (string -> 'a -> 'b) -> int -> 'res
end

let build_default_get_symb (symbs: (var * ty_or_exp) list) =
  let arr = BatArray.of_list symbs in
  let arr = BatArray.map (fun (_, ty_or_exp) ->
      let ty = get_ty_from_tyexp ty_or_exp in
      (ty, default_value ty)
    ) arr
  in
  fun (record_cnstrs : int -> 'c) (record_fns: (int * int) -> 'a -> 'b) i ->
    let tyv = BatArray.get arr i in
    unembed_value record_cnstrs record_fns (fst tyv) (snd tyv)

let defaultSymbolics symbs =
  let get_symb = build_default_get_symb symbs in
  (module
   struct
     let get_symb = Obj.magic get_symb
   end : PackedSymbolics)
