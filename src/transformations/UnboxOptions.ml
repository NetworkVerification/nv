open Collections
open Syntax
open Solution
open OCamlUtils

let rec empty_pattern ty =
  match Typing.canonicalize_type ty with
  | TUnit
  | TBool
  | TInt _
  | TNode
  | TEdge
  | TOption _
  | TMap _
  | TRecord _ ->
    PWild
  | TVar {contents= Link t} ->
    empty_pattern t
  | TTuple ts ->
    PTuple (BatList.map empty_pattern ts)
  | TVar _ | QVar _ | TArrow _ ->
    failwith ("internal error (empty_pattern): " ^ (Printing.ty_to_string ty))

let rec unbox_ty ty =
  match Typing.canonicalize_type ty with
  | TVar {contents= Link t} -> unbox_ty t
  | TBool | TInt _ | TNode | TEdge -> ty
  | TUnit -> TBool
  | TArrow (t1, t2) ->
    TArrow (unbox_ty t1, unbox_ty t2)
  | TTuple ts -> TTuple (BatList.map unbox_ty ts)
  | TOption t -> TTuple [TBool; (unbox_ty t)]
  | TMap (ty1, ty2) ->
    TMap (unbox_ty ty1, unbox_ty ty2)
  | TRecord _ -> failwith "should be unrolled to a tuple"
  | QVar _ | TVar _ -> failwith ("internal error (unbox_ty): " ^ Printing.ty_to_string ty)

let rec unbox_val v =
  match v.v with
  | VUnit ->  aexp(vbool true |> exp_of_value, Some TBool, v.vspan)
  | VBool _ | VInt _ | VNode _ | VEdge _->
    exp_of_value v
  | VOption None ->
    (match v.vty with
     | Some (TOption t) ->
       aexp (etuple [(vbool false |> exp_of_value);
                     (Generators.default_value_exp (Typing.canonicalize_type @@ unbox_ty t))],
             Some (unbox_ty (TOption t)), v.vspan)
     | _ -> failwith "expected option type")
  | VOption (Some v1) ->
    aexp (etuple [(vbool true |> exp_of_value); (unbox_val v1)],
          Some (unbox_ty (oget v.vty)), v.vspan)
  | VTuple vs ->
    aexp (etuple (BatList.map unbox_val vs), Some (unbox_ty (oget v.vty)), v.vspan)
  | VClosure _ -> failwith "Closures not yet implemented"
  | VMap _ -> failwith "no map values"
  | VRecord _ -> failwith "no record values"

let rec unbox_exp e : exp =
  match e.e with
  | ETy (e, ty) -> unbox_exp e
  | EVal v ->
    unbox_val v
  | EVar _ -> aexp(e, Some (unbox_ty (oget e.ety)), e.espan)
  | EFun f ->
    aexp (efun
            { f with
              argty= Some (unbox_ty (oget f.argty));
              resty= Some (unbox_ty (oget f.resty));
              body= unbox_exp f.body },
          Some (unbox_ty (TArrow (oget f.argty, oget f.resty))), e.espan)
  | EApp (e1, e2) ->
    aexp (eapp (unbox_exp e1) (unbox_exp e2), Some (unbox_ty (oget e.ety)), e.espan)
  | EIf (e1, e2, e3) ->
    aexp (eif (unbox_exp e1) (unbox_exp e2) (unbox_exp e3),
          Some (unbox_ty (oget e.ety)), e.espan)
  | ELet (x, e1, e2) ->
    (* The commented piece of code is the correct way to do this
       transformation. The problem is I don't know how to do it in
       conjunction with tuple flattening *)
    (* (match (oget e1.ety) with *)
    (*  | TOption ty -> *)
    (*     aexp (ematch (unbox_exp e1) *)
    (*                  [(PTuple [PVar (proj_var 0 x); PVar (proj_var 1 x)], unbox_exp e2)], *)
    (*           Some (unbox_ty (oget e.ety)), e.espan) *)
    (*  | _ -> *)
    (*     aexp(elet x (unbox_exp e1) (unbox_exp e2), *)
    (*          Some (unbox_ty (oget e.ety)), e.espan)) *)
    aexp(elet x (unbox_exp e1) (unbox_exp e2),
         Some (unbox_ty (oget e.ety)), e.espan)
  | ETuple es ->
    aexp (etuple (BatList.map unbox_exp es), Some (unbox_ty (oget e.ety)), e.espan)
  | ESome e1 ->
    let p1 = aexp (e_val (vbool true), Some TBool, Span.default) in
    let p2 = aexp (unbox_exp e1, Some (unbox_ty (oget e1.ety)), Span.default) in
    aexp (etuple [p1;p2], Some (unbox_ty (oget e.ety)), Span.default)
  | EMatch (e1, bs) ->
    (* Printf.printf "match expr: %s" (Printing.exp_to_string e); *)
    aexp (ematch (unbox_exp e1) (unbox_branches bs (oget e1.ety)),
          Some (unbox_ty (oget e.ety)),
          e.espan)
  | EOp (op, es) -> (
      match (op, es) with
      | And, _
      | Or, _
      | Not, _
      | UAdd _, _
      | USub _, _
      | Eq, _
      | ULess _, _
      | AtMost _, _
      | ULeq _, _
      | MCreate, _
      | MGet, _
      | MSet, _
      | NLess, _
      | NLeq, _
      | TGet _, _
      | TSet _, _ ->
        aexp (eop op (BatList.map unbox_exp es),
              Some (unbox_ty (oget e.ety)), e.espan)
      | _ -> failwith "TODO: implement option unboxing for rest of map operations")
  | ERecord _ | EProject _ ->
    failwith "Record operation in option unboxing"

and unbox_branches bs ty =
  let rec unbox_pattern p ty =
    let ty = get_inner_type ty in
    match p with
    | POption None ->
      (match ty with
       | TOption t ->
         let ps = empty_pattern t in
         PTuple [(PBool false);ps]
       | _ ->
         failwith "must match on option type")
    | POption (Some p) ->
      (match ty with
       | TOption t ->
         PTuple [(PBool true); unbox_pattern p t]
       | _ ->
         failwith "must match on option type")
    | PTuple ps ->
      (match ty with
       | TTuple ts ->
         PTuple (BatList.map2 unbox_pattern ps ts)
       | _ ->
         failwith "must match on a tuple type")
    | PVar x ->
      (match ty with
       | TOption t -> p
       (* PTuple [PVar (proj_var 0 x); PVar (proj_var 1 x)] *)
       | _ -> p)
    | PUnit -> PBool true
    | _ -> p
  in
  mapBranches (fun (p, e) -> (unbox_pattern p ty, unbox_exp e)) bs

let unbox_decl d =
  match d with
  | DLet (x, oty, e) -> DLet (x, Some (unbox_ty (oget oty)), unbox_exp e)
  | DMerge e -> DMerge (unbox_exp e)
  | DTrans e ->
    DTrans (unbox_exp e)
  | DInit e ->
    (* Printf.printf "init ty:%s\n" (Syntax.show_exp ~show_meta:true e); *)
    DInit (unbox_exp e)
  | DAssert e -> DAssert (unbox_exp e)
  | DRequire e -> DRequire (unbox_exp e)
  | DSymbolic (x, Exp e) -> DSymbolic (x, Exp (unbox_exp e))
  | DSymbolic (x, Ty ty) -> DSymbolic (x, Ty (unbox_ty ty))
  | DATy aty -> DATy (unbox_ty aty)
  | DUserTy (x, ty) -> DUserTy (x, unbox_ty ty)
  | DNodes _ | DEdges _ -> d

let unbox ds = BatList.map unbox_decl ds

let rec box_val v ty =
  match v.v, ty with
  | VTuple [vflag; vval], TOption ty ->
    (match vflag.v with
     | VBool false -> voption None
     | VBool true -> voption (Some (box_val vval ty))
     | _ ->
       Printf.printf "%s\n" (Printing.value_to_string vflag);
       failwith "mistyped optional value")
  | VTuple vs, TTuple ts ->
    vtuple (BatList.map2 (box_val) vs ts)
  | VTuple vs, _ ->
    (* Printf.printf "%s\n" (printList (Printing.ty_to_string) ts "" "," ""); *)
    Printf.printf "%s\n" (printList (Printing.value_to_string) vs "" "," "");
    Printf.printf "%s\n" (Printing.ty_to_string ty);
    failwith "mistyped value"
  | VBool _, TUnit -> vunit ()
  | VBool _, _ | VInt _, _ | VNode _, _ | VEdge _, _ -> v
  | VUnit, _ | VOption _, _ | VClosure _, _ | VMap _, _ | VRecord _, _ -> failwith "no such values"

let box_sol ty sol =
  {sol with
   labels = AdjGraph.VertexMap.map (fun v ->
       (* Printf.printf "%s\n" (Printing.value_to_string v); *)
       (* Printf.printf "%s\n" (Printing.ty_to_string ty); *)
       box_val v ty) sol.labels
  }

let unbox_net net =
  { attr_type = unbox_ty net.attr_type;
    init = unbox_exp net.init;
    trans = unbox_exp net.trans;
    merge = unbox_exp net.merge;
    assertion = (match net.assertion with
        | None -> None
        | Some e -> Some (unbox_exp e));
    symbolics = BatList.map (fun (x,e) ->
        match e with
        | Ty ty -> (x, Ty (unbox_ty ty))
        | Exp e -> (x, Exp (unbox_exp e))) net.symbolics;
    defs = BatList.map (fun (x, oty, e) -> (x, Some (unbox_ty (oget oty)), unbox_exp e))
        net.defs;
    utys = BatList.map (fun m ->
        Collections.StringMap.map unbox_ty m) net.utys;
    requires = BatList.map unbox_exp net.requires;
    graph = net.graph
  }, box_sol net.attr_type

let unbox_srp (srp : Syntax.srp_unfold) =
  let unboxed_attr = unbox_ty srp.srp_attr in
  { srp_attr = unboxed_attr;
    srp_constraints = AdjGraph.VertexMap.map unbox_exp srp.srp_constraints;
    srp_labels = AdjGraph.VertexMap.map
        (fun xs -> BatList.map (fun (x,ty) -> (x, unboxed_attr)) xs) srp.srp_labels;
    srp_symbolics =  BatList.map (fun (x,e) ->
        match e with
        | Ty ty -> (x, Ty (unbox_ty ty))
        | Exp e -> (x, Exp (unbox_exp e))) srp.srp_symbolics;
    srp_assertion = (match srp.srp_assertion with
        | None -> None
        | Some e -> Some (unbox_exp e));
    srp_requires = BatList.map unbox_exp srp.srp_requires;
    srp_graph = srp.srp_graph
  }, box_sol srp.srp_attr
