(* Replaces all 0-element tuples in the program with unit,
   and all 1-element tuples with their only element. *)

open Nv_lang
open Syntax
open Nv_utils.OCamlUtils
open Nv_solution

let ty_transformer (recursors : Transformers.recursors) ty =
  match ty with
  | TTuple [] -> Some TUnit
  | TTuple [ty] -> Some (recursors.recurse_ty ty)
  | _ -> None
;;

let pattern_transformer (recursors : Transformers.recursors) p pty =
  match p, pty with
  | PTuple [], TTuple [] -> Some PUnit
  | PTuple [p], TTuple [t] -> Some (recursors.recurse_pattern p t)
  | PTuple [], _ | PTuple [_], _ -> failwith "CleanupTuples: Unexpected pattern type"
  | _ -> None
;;

let value_transformer (recursors : Transformers.recursors) v =
  match v.v with
  | VTuple [] -> Some (vunit ())
  | VTuple [v] -> Some (recursors.recurse_value v)
  | _ -> None
;;

let exp_transformer (recursors : Transformers.recursors) e =
  let cleanup_exp = recursors.recurse_exp in
  match e.e with
  | ETuple [] -> Some (e_val (avalue (vunit (), Some TUnit, e.espan)))
  | ETuple [e] -> Some (cleanup_exp e)
  | EOp (op, es) ->
    begin
      match op, es with
      | TGet (size, _, _), [e1] ->
        if size = 0
        then Some (e_val (avalue (vunit (), Some TUnit, e1.espan)))
        else if size = 1
        then Some (cleanup_exp e1)
        else None
      | TSet (size, _, _), [e1; e2] ->
        if size = 0
        then Some (e_val (avalue (vunit (), Some TUnit, e1.espan)))
        else if size = 1
        then Some (cleanup_exp e2)
        else None
      | (TGet _ | TSet _), _ -> failwith "Bad TGet/TSet"
      | _ -> None (* No other ops take tuples as arguments, so no need to recurse *)
    end
  | _ -> None
;;

(** Functions to convert a solution to the cleanup'd version to a solution
    to the original version **)

let rec map_back_transformer recurse _ v oldty =
  match v.v, oldty with
  | VUnit, TTuple [] -> Some (vtuple [])
  | VBool _, TTuple [] -> Some (vtuple [])
  | _, TTuple [] -> (print_endline (Printing.value_to_string v); failwith "Cleanup Tuples: Unexpected map_back")
  | _, TTuple [oldty'] -> Some (vtuple [recurse v oldty'])
  | _ -> None
;;

let mask_transformer recurse _ v oldty =
  match v.v, oldty with
  | VBool _, TTuple [] -> Some (vtuple [])
  | _, TTuple [] -> failwith "Cleanup Tuples: Unexpected mask"
  | _, TTuple [oldty'] -> Some (vtuple [recurse v oldty'])
  | _ -> None
;;

let make_toplevel (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer
    ~name:"CleanupTuples"
    ty_transformer
    pattern_transformer
    value_transformer
    exp_transformer
    map_back_transformer
    mask_transformer
;;

let cleanup_declarations = make_toplevel Transformers.transform_declarations
