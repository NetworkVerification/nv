open Nv_lang
open Collections
open Syntax
open Nv_solution
open Nv_datastructures
open Nv_utils.OCamlUtils

let ty_transformer (recursors : Transformers.recursors) ty =
  match ty with
  | TOption t ->
    (* If we write something like "let x = None in 5", the particular option type
       of x will be unbound. So for unboxing purposes, replace it with unit *)
    let t =
      match t with
      | TVar { contents = Unbound _ } -> TUnit
      | _ -> t
    in
    Some (TTuple [TBool; recursors.recurse_ty t])
  | _ -> None
;;

let pattern_transformer (recursors : Transformers.recursors) p ty =
  match p, ty with
  | POption None, TOption _ -> Some (PTuple [PBool false; PWild])
  | POption (Some p), TOption t ->
    Some (PTuple [PBool true; recursors.recurse_pattern p t])
  | _ -> None
;;

let value_transformer (recursors : Transformers.recursors) v =
  match v.v with
  | VOption None ->
    (* This takes advantage of the fact that the default value for bools is false *)
    Some (Generators.default_value (recursors.recurse_ty (oget v.vty)))
  | VOption (Some v) ->
    Some (vtuple [avalue (vbool true, Some TBool, v.vspan); recursors.recurse_value v])
  | _ -> None
;;

let exp_transformer (recursors : Transformers.recursors) e =
  match e.e with
  | ESome e' ->
    Some
      (etuple
         [ aexp (e_val (avalue (vbool true, Some TBool, e.espan)), Some TBool, e.espan)
         ; recursors.recurse_exp e' ])
  | _ -> None
;;

let map_back_transformer recurse _ v orig_ty =
  match v.v, orig_ty with
  | VTuple [vflag; vval], TOption ty ->
    (match vflag.v with
    | VBool false -> Some (voption None)
    | VBool true -> Some (voption (Some (recurse vval ty)))
    | _ ->
      Printf.printf "%s\n" (Printing.value_to_string vflag);
      failwith "mistyped optional value")
  | _ -> None
;;

(* Conveniently this happens to work *)
let mask_transformer = map_back_transformer

let make_toplevel (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer
    ~name:"UnboxOptions"
    ty_transformer
    pattern_transformer
    value_transformer
    exp_transformer
    map_back_transformer
    mask_transformer
;;

let unbox_declarations = make_toplevel Transformers.transform_declarations
