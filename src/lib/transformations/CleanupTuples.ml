(* Replaces all 0-element tuples in the program with unit,
   and all 1-element tuples with their only element. *)

open Nv_lang
open Syntax
open Nv_utils.OCamlUtils
open Nv_solution

let ty_mutator _ ty =
  match ty with
  | TTuple [] -> Some(TUnit)
  | TTuple [ty] -> Some(ty)
  | _ -> None
;;

let pattern_mutator _ p _ =
  match p with
  | PTuple [] -> Some(PUnit)
  | PTuple [p] -> Some(p)
  | _ -> None
;;

let value_mutator _ v =
  match v.v with
  | VTuple [] -> Some(vunit ())
  | VTuple [v] -> Some(v)
  | _ -> None
;;

let exp_mutator (recursors: Mutators.recursors) e =
  let cleanup_exp = recursors.recurse_exp in
  match e.e with
  | ETuple [] -> Some (e_val (avalue (vunit (), Some TUnit, e.espan)))
  | ETuple [e] -> Some(e)
  | EOp (op, es) ->
    begin
      match op, es with
      | TGet (size, _, _), [e1] ->
        if size = 0 then Some (e_val (avalue (vunit (), Some TUnit, e1.espan)))
        else if size = 1 then Some (cleanup_exp e1)
        else None
      | TSet (size, _, _), [e1; e2] ->
        if size = 0 then Some (e_val (avalue (vunit (), Some TUnit, e1.espan)))
        else if size = 1 then Some(cleanup_exp e2)
        else None
      | (TGet _ | TSet _), _ -> failwith "Bad TGet/TSet"
      | _ -> None (* No other ops take tuples as arguments, so no need to recurse *)
    end
  | _ -> None
;;

(** Functions to convert a solution to the cleanup'd version to a solution
    to the original version **)

let rec map_back_mutator _ _ v oldty =
  match v.v, oldty with
  | VUnit, TTuple [] -> Some(vtuple [])
  | _, TTuple [_] -> Some(vtuple [v])
  | _ -> None
;;

let mask_mutator _ _ v oldty =
  match v.v, oldty with
  | VBool _, TTuple [] -> Some (vtuple [])
  | _, TTuple [_] -> Some(vtuple [v])
  | _ -> None
;;

let make_toplevel (toplevel_mutator : 'a Mutators.toplevel_mutator) =
  toplevel_mutator ~name:"CleanupTuples" ty_mutator pattern_mutator value_mutator exp_mutator map_back_mutator mask_mutator
;;

let cleanup_declarations = make_toplevel Mutators.mutate_declarations
let cleanup_net = make_toplevel Mutators.mutate_network
let cleanup_srp = make_toplevel Mutators.mutate_srp
