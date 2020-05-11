open Batteries
open Nv_lang.Syntax

(* Replace all instances of Unit with booleans (set to false), so we don't
   have to deal with them during SMT encoding *)

let ty_transformer _ ty =
  match ty with
  | TUnit -> Some TBool
  | _ -> None
;;

let pattern_transformer _ p _ =
  match p with
  | PUnit -> Some PWild (* Preserves irrefutability *)
  | _ -> None
;;

let value_transformer _ v =
  match v.v with
  | VUnit -> Some (vbool false)
  | _ -> None
;;

let exp_transformer _ _ = None;;

let map_back_transformer _ _ v orig_ty =
  match v.v, orig_ty with
  | VBool false, TUnit -> Some (vunit ())
  | _ -> None
;;

(* Bools and Unit have the same mask type *)
let mask_transformer _ _ v _ = Some v;;

let make_toplevel (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer ~name:"UnboxUnits" ty_transformer pattern_transformer value_transformer exp_transformer map_back_transformer mask_transformer
;;

let unbox_declarations = make_toplevel Transformers.transform_declarations