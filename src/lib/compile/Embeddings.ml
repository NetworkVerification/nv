(** * OCaml to NV Embeddings*)
open Nv_lang
open Nv_utils
open Nv_datastructures
open PrimitiveCollections
open Syntax

(* TODO: cache calls to embed and unembed, based on type, but potentially based on value too *)

(** Given an NV type and an OCaml value constructs an NV value*)
let rec embed_value (record_fns: string -> 'a -> 'b) (typ: Syntax.ty) : 'a -> Syntax.value =
  match typ with
    | TUnit ->
      fun _ -> Syntax.vunit ()
    | TBool ->
      fun v -> Syntax.vbool (Obj.magic v)
    | TInt _ ->
      fun v -> Syntax.vint ((Obj.magic v) |> Integer.of_int)
    | TOption ty ->
      let f = embed_value record_fns ty in
        Obj.magic (fun v ->
            (match v with
              | None -> Syntax.voption None
              | Some v' -> Syntax.voption (Some (f v'))))
    | TTuple ts ->
      let n = BatList.length ts in
      let fs = BatList.mapi (fun i ty ->
          let proj_fun = Printf.sprintf "p%d__%d" i n in
          let f_rec = embed_value record_fns ty in
          let proj_val = record_fns proj_fun in
            fun v ->
              let vrec = v in
                f_rec (proj_val vrec)) ts
      in
        fun v -> Syntax.vtuple (BatList.map (fun f -> f v) fs)
    | TMap _ -> (* trivial as we represent maps with the same mtbdd + value type*)
      fun v -> Syntax.vmap (fst (Obj.magic v))
    | TArrow _ -> failwith "Function computed as value"
    | TRecord _ -> failwith "Trecord"
    | TNode -> failwith "Tnode"
    | TEdge -> failwith "Tedge"
    | TVar _ | QVar _ -> failwith "TVars and QVars shuld not show up here"

(** Takes an NV value of type typ and returns an OCaml value.*)
let rec unembed_value (record_cnstrs : string -> 'c) (record_proj : string -> 'a -> 'b)
    (typ: Syntax.ty) : Syntax.value -> 'a =
  match typ with
    | TUnit ->
      fun _ -> ()
    | TBool ->
      fun v ->
        (match v.v with
          | VBool b -> Obj.magic b
          | _ -> failwith "mistyped value")
    | TInt _ ->
      fun v ->
        (match v.v with
          | VInt i -> Obj.magic (Integer.to_int i) (*NOTE: We translate UInts to ints but we need to change that *)
          | _ -> failwith "mistyped value")
    | TOption ty ->
      let f = unembed_value record_cnstrs record_proj ty in
        Obj.magic (fun v ->
            match v.v with
              | VOption None -> None
              | VOption (Some v') -> Some (f v')
              | _ -> failwith "mistyped value")
    | TTuple ts ->
      (*TODO: this case is wrong, fix it*)
      let n = BatList.length ts in
      let f_cnstr = record_cnstrs (string_of_int n) in (*function that constructs the record*)
      let fs = (*functions that unembed each value of a tuple *)
        BatList.map (fun ty -> unembed_value record_cnstrs record_proj ty) ts
      in
        fun v ->
          (match v.v with
            | VTuple vs ->
              BatList.fold_left2 (fun acc f v -> Obj.magic (acc (f v))) f_cnstr fs vs
              |> Obj.magic
            | _ -> failwith "mistyped value")
    | TMap (_, vty) ->
      (* this is trivial as OCaml maps are NV maps plus a value type*)
      fun v ->
        (match v.v with
          | VMap vdd -> Obj.magic (vdd, vty)
          | _ -> failwith "mistyped value")
    | TArrow _ -> failwith "Function computed as value"
    | TRecord _ -> failwith "Trecord"
    | TNode -> failwith "Tnode"
    | TEdge -> failwith "Tedge"
    | TVar _ | QVar _ -> failwith "TVars and QVars shuld not show up here"
