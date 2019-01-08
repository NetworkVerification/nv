open Syntax
open RecordUtils

let rec unroll_type
    (rtys : ty StringMap.t list)
    (ty : ty)
  : ty
  =
  (* print_endline @@  "Unrolling type: " ^ Printing.ty_to_string ty; *)
  let unroll_type = unroll_type rtys in
  (* let ty = canonicalize_type ty in *)
  match ty with
  | TBool
  | TInt _
  | QVar _ ->
    ty
  | TArrow (t1, t2) ->
    TArrow (unroll_type t1, unroll_type t2)
  | TTuple tys ->
    TTuple (List.map unroll_type tys)
  | TOption ty ->
    TOption (unroll_type ty)
  | TMap (key_ty, val_ty) ->
    TMap (unroll_type key_ty, unroll_type val_ty)
  | TRecord map ->
    TTuple (get_record_entries map)
  | TVar _ ->
    failwith "Encountered TVar after canonicalization"
;;

let rec unroll_exp
    (rtys : ty StringMap.t list)
    (e : exp)
  : exp
  =
  let unroll_exp e = unroll_exp rtys e in
  let unrolled_exp =
    match e.e with
    | EVal _ (* No way to construct record value directly *)
    | EVar _ ->
      exp e.e
    | EFun f ->
      efun
        { f with
          argty= None; resty= None; body= unroll_exp f.body }
    | EApp (e1, e2) ->
      eapp (unroll_exp e1) (unroll_exp e2)
    | EIf (e1, e2, e3) ->
      eif (unroll_exp e1) (unroll_exp e2) (unroll_exp e3)
    | ELet (x, e1, e2) ->
      elet x (unroll_exp e1) (unroll_exp e2)
    | ETuple es ->
      etuple (List.map unroll_exp es)
    | ESome e1 ->
      esome (unroll_exp e1)
    | EMatch (e1, bs) ->
      ematch
        (unroll_exp e1)
        (List.map (fun (p, e) -> (p, unroll_exp e)) bs)
    | ETy (e1, _) -> unroll_exp e1
    | EOp (op, es) -> eop op (List.map unroll_exp es)
    | ERecord map ->
      etuple (List.map unroll_exp @@ get_record_entries map)
    | EProject (e1, l) ->
      let rty = get_type_with_label rtys failwith l in
      let labels = get_record_labels rty in
      let idx = oget @@ BatList.index_of l labels in
      (* Extract tuple element at index idx *)
      let var = Var.fresh "recordUnrolling" in
      let ps =
        List.mapi
          (fun i _ -> if i = idx then PVar var else PWild)
          labels
      in
      let tpattern = PTuple ps in
      ematch (unroll_exp e1) [(tpattern, evar var)]
  in
  aexp (unrolled_exp, None, e.espan)
;;

let rec unroll_decl
    (rtys : ty StringMap.t list)
    (decl : declaration)
  : declaration
  =
  let unroll_exp = unroll_exp rtys in
  let unroll_type = unroll_type rtys in
  match decl with
  | DLet (var, tyo, e) ->
    let tyo' =
      match tyo with
      | Some t -> Some(unroll_type t)
      | None -> None
    in
    DLet (var, tyo', unroll_exp e)
  | DSymbolic (var, toe) ->
    let toe' =
      match toe with
      | Ty t -> Ty(unroll_type t)
      | Exp e -> Exp(unroll_exp e)
    in
    DSymbolic (var, toe')
  | DATy t -> DATy (unroll_type t)
  | DUserTy (s, t) -> DUserTy (s, unroll_type t)
  | DMerge e -> DMerge (unroll_exp e)
  | DTrans e -> DTrans (unroll_exp e)
  | DInit e -> DInit (unroll_exp e)
  | DAssert e -> DAssert (unroll_exp e)
  | DRequire e -> DRequire (unroll_exp e)
  | DNodes _
  | DEdges _ -> decl
;;

(* Conversion functions for translating tupleized types back into
   record types *)
let rec convert_value
    (original_ty : ty)
    (v : value)
  : value
  =
  (* TODO: Potentially add on span and type info *)
  match v.v, original_ty with
  | VBool _, TBool
  | VInt _, TInt _ ->
    v
  | VOption vo, TOption t ->
    begin
      match vo with
      | None -> voption None
      | Some v' -> voption (Some (convert_value t v'))
    end
  | VTuple vs, TTuple ts ->
    vtuple (List.map2 convert_value ts vs)
  | VTuple vs, TRecord tmap ->
    (* We found a converted record; convert it back *)
    let labels = get_record_labels tmap in
    let vmap = List.fold_left2
        (fun map k v ->  StringMap.add k v map)
        StringMap.empty labels vs
    in
    vrecord vmap
  | VMap m, TMap (kty, vty) ->
    (* This could very well be wrong *)
    let default = default_value vty in
    let base = BddMap.create ~key_ty:kty default in
    let bindings, _ = BddMap.bindings m in
    let newbdd, _ =
      List.fold_left
        (fun acc (k, v) -> BddMap.update acc k (convert_value vty v))
        base bindings
    in
    vmap (newbdd, kty)
  | VRecord _, _ ->
    failwith "convert_value: found record while converting back to records"
  | VClosure _, TArrow _ ->
    failwith "convert_value: Cannot convert function value"
  | _ ->
    failwith "convert_value: type and value do not match"
;;

let convert_symbolics
    (decls : declarations)
    (sol : Solution.t)
  =
  let symbolics = get_symbolics decls in
  let convert_symbolic symb v =
    let _, toe =
      List.find
        (* Maybe this should be Var.name s? *)
        (fun (s, _) -> String.equal (Var.to_string s) symb)
        symbolics
    in
    let oldty =
      match toe with
      | Ty ty -> ty
      | Exp e -> oget e.ety
    in
    convert_value oldty v
  in
  let new_symbolics =
    StringMap.mapi convert_symbolic sol.symbolics
  in
  new_symbolics
;;

let convert_attrs
    (decls : declarations)
    (sol : Solution.t)
  =
  let attr_ty = oget (get_attr_type decls) in
  AdjGraph.VertexMap.map
    (fun v -> convert_value attr_ty v)
    sol.labels
;;

let unroll decls =
  let rtys = get_record_types decls in
  let unrolled = List.map (unroll_decl rtys) decls in
  print_endline @@ Printing.declarations_to_string unrolled;
  let map_back sol =
    let new_symbolics = convert_symbolics decls sol in
    let new_labels = convert_attrs decls sol in
    {sol with symbolics = new_symbolics; labels = new_labels}
  in
  unrolled, map_back
