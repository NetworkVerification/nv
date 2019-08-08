open Batteries
open Nv_lang.Syntax

(* Replace all instances of Unit with booleans (set to false), so we don't
   have to deal with them during SMT encoding *)

let ty_mutator _ ty =
  match ty with
  | TUnit -> Some TBool
  | _ -> None
;;

let pattern_mutator _ p _ =
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

let make_toplevel (toplevel_mutator : 'a Mutators.toplevel_mutator) =
  toplevel_mutator ~name:"UnboxOptions" ty_mutator pattern_mutator value_mutator exp_mutator map_back_mutator mask_mutator
;;

let unbox_declarations = make_toplevel Mutators.mutate_declarations
let unbox_net = make_toplevel Mutators.mutate_network
let unbox_srp = make_toplevel Mutators.mutate_srp
