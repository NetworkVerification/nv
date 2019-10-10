open Nv_lang
open Syntax
open BddMap
open Embeddings

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
  fun (record_cnstrs : string -> 'c) (record_fns: string -> 'a -> 'b) i ->
    let tyv = BatArray.get arr i in
    unembed_value record_cnstrs record_fns (fst tyv) (snd tyv)

let defaultSymbolics symbs =
  let get_symb = build_default_get_symb symbs in
  (module
   struct
     let get_symb = Obj.magic get_symb
   end : PackedSymbolics)
