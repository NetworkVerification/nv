open Syntax
open Collections
open MapUnrollingGuts
open Typing

(* e must be a literal *)
let rec exp_to_value (e : exp) : value =
  match e.e with
  | EVar _
  | EOp _
  | EFun _
  | EApp _
  | EIf _
  | ELet _
  | EMatch _
  | EProject _ ->
     failwith
       (Printf.sprintf "MapUnrollingConversions internal error on: %s"
                       (Printing.exp_to_string e))
  | ESome exp2 ->
    voption (Some (exp_to_value exp2))
  | ETuple es ->
    vtuple (List.map exp_to_value es)
  | EVal v -> v
  | ETy (exp2, _) -> exp_to_value exp2
  | ERecord map -> vrecord (StringMap.map exp_to_value map)

let rec convert_value
    (ty : ty)
    (keys : exp list)
    (v : value)
    (original_ty : ty)
  : value
  =
  (* TODO: Potentially add on span and type info *)
  let convert_value = convert_value ty keys in
  match v.v, (canonicalize_type original_ty) with
  | VBool _, TBool
  | VInt _, TInt _ ->
    v
  | VOption vo, TOption t ->
    begin
      match vo with
      | None -> voption None
      | Some v' -> voption (Some (convert_value v' t))
    end
  | VTuple vs, TTuple ts ->
    vtuple (List.map2 convert_value vs ts)
  | VTuple vs, TMap (kty, vty) ->
    (* We found a converted map; convert it back *)
    let default = default_value vty in
    let bindings = List.combine (List.map exp_to_value keys) vs in
    let newmap = BddMap.from_bindings ~key_ty:kty (bindings, default) in
    vmap newmap
  | VMap m, TMap (kty, vty) ->
    (* Non-converted map; recurse on its values. Don't have to look at
       key type since we can't have key types involving maps *)
    let unrolled_vty = unroll_type ty keys vty in
    if Typing.equiv_tys vty unrolled_vty
    then v (* No change to value type *)
    else (* value type contains our map type *)
      let bindings, default = BddMap.bindings m in
      let newmap = BddMap.from_bindings ~key_ty:kty (bindings, default) in
      vmap newmap
  | VClosure _, TArrow _ ->
    failwith "convert_value: Cannot convert function value"
  | VRecord _, TRecord _ -> failwith "convert_value: encountered record value"
  | _ ->
    failwith "convert_value: type and value do not match"
;;

let convert_symbolics
    (ty : ty)
    (keys : exp list)
    (decls : declarations)
    (sol : Solution.t)
  =
  let symbolics = get_symbolics decls in
  let convert_value = convert_value ty keys in
  let symbolics_to_convert =
    BatList.filter_map
      (fun (v, e) ->
         let oldty = match e with Ty ty -> ty | Exp e -> oget e.ety in
         let newty = unroll_type ty keys oldty in
         if Typing.equiv_tys oldty newty then None
         else Some (Var.to_string v, oldty))
      symbolics
  in
  let convert_symbolic var v =
    let symb =
      List.find_opt
        (fun (var', _) -> String.equal var var')
        symbolics_to_convert
    in
    match symb with
    | None -> v
    | Some(_, original_ty) ->
      convert_value v original_ty
  in
  let new_symbolics =
    StringMap.mapi convert_symbolic sol.symbolics
  in
  new_symbolics

let convert_attrs
    (ty : ty)
    (keys : exp list)
    (decls : declarations)
    (sol : Solution.t)
  =
  let attr_ty = oget (get_attr_type decls) in
  let unrolled_attr_ty = unroll_type ty keys attr_ty in
  if Typing.equiv_tys attr_ty unrolled_attr_ty then sol.labels
  else (* Attribute type involved a map, so transform all attributes *)
    AdjGraph.VertexMap.map
      (fun v -> convert_value ty keys v attr_ty)
      sol.labels
;;

(* Given the map type and keys, return a function which will convert a
   solution to the unrolled version into a solution to the original *)
let convert_solution
    (ty : ty)
    (keys : exp list)
    (decls : declarations)
    (sol : Solution.t)
  : Solution.t
  =
  let new_symbolics = convert_symbolics ty keys decls sol in
  let new_labels = convert_attrs ty keys decls sol in
  {sol with symbolics = new_symbolics; labels = new_labels}
;;
