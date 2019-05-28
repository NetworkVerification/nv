open Syntax
open RecordUtils


(* Re-copying that here, to turn Unbound tvars into unbound tvars instead of TBool.
   We do the TBool thing, such that the SMT can handle those values (e.g. unused None).
   In general, I think we shouldn't have unbound Tvars... they should have been generalized
   to qvars *)
let canonicalize_type (ty : ty) : ty =
  let open Collections in
  let rec aux ty map count =
    match ty with
    | TBool
    | TInt _ ->
      ty, map, count
    | TArrow (t1, t2) ->
      let t1', map, count = aux t1 map count in
      let t2', map, count = aux t2 map count in
      TArrow (t1', t2'), map, count
    | TTuple (tys) ->
      let tys', map, count =
        BatList.fold_left
          (fun (lst, map, count) t ->
             let t', map, count = aux t map count in
             t' :: lst, map, count
          )
          ([], map, count) tys
      in
      TTuple (BatList.rev tys'), map, count
    | TRecord (tmap) ->
      let tmap', map, count =
        BatList.fold_left2
          (fun (tmap, map, count) l t ->
             let t', map, count = aux t map count in
             StringMap.add l t' tmap, map, count
          )
          (StringMap.empty, map, count) (get_record_labels tmap) (get_record_entries tmap)
      in
      TRecord tmap', map, count
    | TOption t ->
      let t', map, count = aux t map count in
      TOption (t'), map, count
    | TMap (t1, t2) ->
      let t1', map, count = aux t1 map count in
      let t2', map, count = aux t2 map count in
      TMap (t1', t2'), map, count
    | QVar tyname ->
      begin
        match VarMap.find_opt tyname map with
        | None ->
          let new_var = Var.to_var ("a", count) in
          ( QVar (new_var),
            (VarMap.add tyname new_var map),
            count + 1)
        | Some v -> QVar (v), map, count
      end
    | TVar r ->
      begin
        match !r with
        | Link t -> aux t map count
        | Unbound _ -> ty, map, count
      end
  in
  let (result, _, _) = aux ty (VarMap.empty) 0 in
  result

let rec unroll_type
    (rtys : ty StringMap.t list)
    (ty : ty)
  : ty
  =
  (* print_endline @@  "Unrolling type: " ^ Printing.ty_to_string ty; *)
  let unroll_type = unroll_type rtys in
  let ty = canonicalize_type ty in
  match ty with
  | TBool
  | TInt _
  | QVar _ ->
    ty
  | TArrow (t1, t2) ->
    TArrow (unroll_type t1, unroll_type t2)
  | TTuple tys ->
    TTuple (BatList.map unroll_type tys)
  | TOption ty ->
    TOption (unroll_type ty)
  | TMap (key_ty, val_ty) ->
    TMap (unroll_type key_ty, unroll_type val_ty)
  | TRecord map ->
    TTuple (BatList.map unroll_type (get_record_entries map))
  | TVar _ ->
    ty
;;

let rec unroll_pattern p =
  match p with
  | PWild
  | PInt _
  | PBool _
  | PVar _
  | POption None -> p
  | PTuple ps ->
    PTuple (BatList.map unroll_pattern ps)
  | POption (Some p) ->
    POption (Some (unroll_pattern p))
  | PRecord map ->
    PTuple (BatList.map unroll_pattern (get_record_entries map))
;;

let rec unroll_exp
    (rtys : ty StringMap.t list)
    (e : exp)
  : exp
  =
  let unroll_exp e = unroll_exp rtys e in
  let unroll_type ty = unroll_type rtys ty in
  match e.e with
  | EVal _ (* No way to construct record value directly *)
  | EVar _ ->
    e
  | EFun f ->
    aexp (efun
            { f with
              argty= Some (unroll_type (oget f.argty));
              resty= Some (unroll_type (oget f.resty));
              body= unroll_exp f.body },
          Some (unroll_type (TArrow (oget f.argty, oget f.resty))), e.espan)
  | EApp (e1, e2) ->
    aexp (eapp (unroll_exp e1) (unroll_exp e2), Some (unroll_type (oget e.ety)), e.espan)
  | EIf (e1, e2, e3) ->
    aexp (eif (unroll_exp e1) (unroll_exp e2) (unroll_exp e3),
          Some (unroll_type (oget e.ety)), e.espan)
  | ELet (x, e1, e2) ->
    aexp(elet x (unroll_exp e1) (unroll_exp e2),
         Some (unroll_type (oget e.ety)), e.espan)
  | ETuple es ->
    aexp (etuple (BatList.map unroll_exp es), Some (unroll_type (oget e.ety)), e.espan)
  | ESome e1 ->
    aexp (esome (unroll_exp e1), Some (unroll_type (oget e.ety)), e.espan)
  | EMatch (e1, bs) ->
    aexp (ematch (unroll_exp e1)
            (mapBranches (fun (p,eb) -> (unroll_pattern p, unroll_exp eb)) bs),
          Some (unroll_type (oget e.ety)),
          e.espan)
  | ETy (e1, _) -> unroll_exp e1
  | EOp (op, es) ->
    aexp (eop op (BatList.map unroll_exp es),
          Some (unroll_type (oget e.ety)), e.espan)
  | ERecord map ->
    aexp (etuple (BatList.map unroll_exp @@ get_record_entries map),
          Some (unroll_type (oget e.ety)), e.espan)
  | EProject (e1, l) ->
    let rty = get_type_with_label rtys failwith l in
    let labels = get_record_labels rty in
    let types = get_record_entries rty in
    let idx = oget @@ BatList.index_of l labels in
    let ty = BatList.nth types idx in
    (* Extract tuple element at index idx *)
    let var = Var.fresh "recordUnrolling" in
    let ps =
      BatList.mapi
        (fun i _ -> if i = idx then PVar var else PWild)
        labels
    in
    let tpattern = PTuple ps in
    aexp (ematch (unroll_exp e1) (addBranch tpattern
                                    (aexp (evar var, Some ty, e.espan)) emptyBranch),
          Some ty, e.espan)
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
    vtuple (BatList.map2 convert_value ts vs)
  | VTuple vs, TRecord tmap ->
    (* We found a converted record; convert it back *)
    let labels = get_record_labels tmap in
    let vmap = BatList.fold_left2
        (fun map k v ->  StringMap.add k v map)
        StringMap.empty labels vs
    in
    vrecord vmap
  | VMap m, TMap (kty, vty) ->
    let bindings, default = BddMap.bindings m in
    let default' = convert_value vty default in
    let bindings' =
      BatList.map (fun (k, v) -> k, convert_value vty v) bindings
    in
    let newbdd = BddMap.from_bindings ~key_ty:kty (bindings', default') in
    vmap newbdd
  | VRecord _, _ ->
    failwith "convert_value: found record while converting back to records"
  | VClosure _, TArrow _ ->
    failwith "convert_value: Cannot convert function value"
  | _ ->
    failwith
      (Printf.sprintf "convert_value: value (%s) and type (%s) do not match"
         (Printing.value_to_string v) (Printing.ty_to_string original_ty))
;;

let convert_symbolics
    symbolics
    (sol : Solution.t)
  =
  let convert_symbolic symb v =
    let _, toe =
      BatList.find
        (fun (s, _) ->
             String.equal (Var.name s) symb)
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
    attr_ty
    (sol : Solution.t)
  =
  AdjGraph.VertexMap.map
    (fun v -> convert_value attr_ty v)
    sol.labels
;;

let unroll decls =
  let rtys = get_record_types decls in
  let unrolled = BatList.map (unroll_decl rtys) decls in
  (* print_endline @@ Printing.declarations_to_string unrolled; *)
  let map_back sol =
    let new_symbolics = convert_symbolics (get_symbolics decls) sol in
    let new_labels = convert_attrs (oget (get_attr_type decls)) sol in
    {sol with symbolics = new_symbolics; labels = new_labels}
  in
  unrolled, map_back

let unroll_net_aux
    (rtys : ty StringMap.t list)
    net
  =
  let unroll_exp = unroll_exp rtys in
  let unroll_type = unroll_type rtys in
  { attr_type = unroll_type net.attr_type;
    init = unroll_exp net.init;
    merge = unroll_exp net.merge;
    trans = unroll_exp net.trans;
    symbolics = BatList.map (fun (var, toe) ->
        let toe' =
          match toe with
          | Ty t -> Ty(unroll_type t)
          | Exp e -> Exp(unroll_exp e)
        in
        (var, toe')) net.symbolics;
    defs = BatList.map (fun (var, tyo, e) ->
        let tyo' =
          match tyo with
          | Some t -> Some(unroll_type t)
          | None -> None
        in
        (var, tyo', unroll_exp e)) net.defs;
    utys =
      BatList.map (fun m -> Collections.StringMap.map unroll_type m) net.utys;
    assertion = (match net.assertion with
        | None -> None
        | Some e ->
          Some (unroll_exp e));
    requires = BatList.map unroll_exp net.requires;
    graph = net.graph
  }


let unroll_net net =
  let rtys = net.utys in
  let unrolled = unroll_net_aux rtys net in
  (* print_endline @@ Printing.declarations_to_string unrolled; *)
  let map_back sol =
    let new_symbolics = convert_symbolics net.symbolics sol in
    let new_labels = convert_attrs net.attr_type sol in
    {sol with symbolics = new_symbolics; labels = new_labels}
  in
  unrolled, map_back
