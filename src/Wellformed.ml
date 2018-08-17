open Syntax

(* Check a variety of other requirements for a well-
   formed program. Assumes the program is well-typed *)

let rec has_map ty =
  match get_inner_type ty with
  | TBool | TInt _ | TVar _ | QVar _ -> false
  | TTuple ts -> List.exists has_map ts
  | TArrow (ty1, ty2) -> has_map ty1 || has_map ty2
  | TOption ty -> has_map ty
  | TMap _ -> true

let rec check_type ty : bool =
  match get_inner_type ty with
  | TBool | TInt _ | TVar _ | QVar _ -> true
  | TTuple ts -> List.for_all check_type ts
  | TOption ty -> check_type ty
  | TArrow (ty1, ty2) -> check_type ty1 && check_type ty2
  | TMap (kty, vty) ->
      not (has_map kty) && check_type kty && check_type vty

let check_types info _ (e: exp) =
  let ty = oget e.ety in
  if not (check_type ty) then
    let msg =
      "expression type has dictionary type with dictionary keys"
    in
    Console.error_position info e.espan msg

let check info (ds: declarations) : unit =
  Visitors.iter_exp_decls (check_types info) ds
