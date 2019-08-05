open Batteries
open Nv_lang.Syntax

(* Replace all instances of Unit with booleans (set to false), so we don't
   have to deal with them during SMT encoding *)

let ty_mutator _ ty =
  match ty with
  | TUnit -> Some TBool
  | _ -> None
;;

let pat_mutator _ p =
  match p with
  | PUnit -> Some PWild (* Preserves irrefutability *)
  | _ -> None
;;

let value_mutator _ v =
  match v.v with
  | VUnit -> Some (vbool false)
  | _ -> None
;;

let exp_mutator _ _ = None;;

let map_back_mutator _ v orig_ty =
  match v.v, orig_ty with
  | VBool false, TUnit -> Some (vunit ())
  | _ -> None
;;

(* Bools and Unit have the same mask type *)
let mask_mutator _ v _ = Some v;;

let unbox_declarations = Mutators.mutate_declarations ty_mutator pat_mutator value_mutator exp_mutator map_back_mutator mask_mutator;;
let unbox_net = Mutators.mutate_network ty_mutator pat_mutator value_mutator exp_mutator map_back_mutator mask_mutator;;
