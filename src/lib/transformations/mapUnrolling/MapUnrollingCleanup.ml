(* Replaces all 0-element tuples in the program with unit,
   and all 1-element tuples with their only element *)

open Nv_lang

let mapo f o =
  match o with
  | None -> None
  | Some x -> Some (f x)
;;

let rec replace_ty ty =
  let open Syntax in
  match ty with
  | TUnit | TBool | TInt _ | TNode | TEdge | QVar _ -> ty
  | TTuple [] -> TUnit
  | TTuple [ty'] -> replace_ty ty'
  | TTuple tys -> TTuple (List.map replace_ty tys)
  | TArrow (ty1, ty2) -> TArrow (replace_ty ty1, replace_ty ty2)
  | TOption ty' -> TOption (replace_ty ty')
  | TVar r ->
    begin
      match !r with
      | Link t -> replace_ty t
      | Unbound _ -> ty
    end
  | TMap _ | TRecord _ -> failwith "Should be unrolled"
;;

let rec replace_pattern p =
  let open Syntax in
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PVar _ | PNode _ | PEdge _ -> p
  | PTuple [] -> PUnit
  | PTuple [p] -> replace_pattern p
  | PTuple ps -> PTuple (List.map replace_pattern ps)
  | POption po -> POption (mapo replace_pattern po)
  | PRecord _ -> failwith "Should be unrolled"
;;

let rec replace_val v =
  let open Syntax in
  let new_v =
    match v.v with
    | VUnit | VBool _ | VInt _ | VNode _ | VEdge _ -> v
    | VTuple [] -> vunit ()
    | VTuple [v'] -> replace_val v'
    | VTuple vs -> vtuple (List.map replace_val vs)
    | VOption vo -> voption (mapo replace_val vo)
    | VRecord _ | VMap _ -> failwith "Should be unrolled"
    | VClosure _ -> failwith "Should be inlined"
  in
  avalue (new_v, mapo replace_ty v.vty, v.vspan)
;;

let rec replace_exp e =
  let open Syntax in
  let new_e =
    match e.e with
    | ETuple [] -> e_val (vunit ())
    | ETuple [e] -> e
    | ETuple es -> etuple (List.map replace_exp es)
    | EVar _ -> e
    | EOp (op, es) ->
      begin
        match op, es with
        | TGet (size, _, _), [e1] ->
          if size = 0 then e_val (avalue (vunit (), Some TUnit, e1.espan))
          else if size = 1 then replace_exp e1
          else eop op (List.map replace_exp es)
        | TSet (size, _, _), [e1; e2] ->
          if size = 0 then e_val (avalue (vunit (), Some TUnit, e1.espan))
          else if size = 1 then replace_exp e2
          else eop op (List.map replace_exp es)
        | (TGet _ | TSet _), _ -> failwith "Bad TGet/TSet"
        | _ -> e (* No other ops take tuples as arguments, so no need to recurse *)
      end
    | ETy (e, ty) -> ety (replace_exp e) (replace_ty ty)
    | EVal v -> e_val (replace_val v)
    | ESome e -> esome (replace_exp e)
    | EApp (e1, e2) -> eapp (replace_exp e1) (replace_exp e2)
    | EFun f -> efun { f with
                       argty= mapo replace_ty f.argty;
                       resty= mapo replace_ty f.resty;
                       body= replace_exp f.body }
    | EIf (e1, e2, e3) -> eif (replace_exp e1) (replace_exp e2) (replace_exp e3)
    | ELet (x, e1, e2) -> elet x (replace_exp e1) (replace_exp e2)
    | EMatch (e, branches) -> ematch (replace_exp e)
                                (mapBranches (fun (p, e) -> (replace_pattern p, replace_exp e)) branches)
    | ERecord _ | EProject _ -> failwith "Should be unrolled"
  in
  aexp (new_e, mapo replace_ty e.ety, e.espan)
;;

let replace_toe toe =
  let open Syntax in
  match toe with
  | Ty ty -> Ty (replace_ty ty)
  | Exp e -> Exp (replace_exp e)
;;

let rec replace_decl d =
  let open Syntax in
  match d with
  | DNodes _ | DEdges _ -> d
  | DInit e -> DInit (replace_exp e)
  | DTrans e -> DTrans (replace_exp e)
  | DMerge e -> DMerge (replace_exp e)
  | DAssert e -> DAssert (replace_exp e)
  | DLet (x, tyo, e) -> DLet (x, mapo replace_ty tyo, replace_exp e)
  | DSymbolic (x, toe) -> DSymbolic(x, replace_toe toe)
  | DRequire e -> DRequire (replace_exp e)
  | DATy aty -> DATy (replace_ty aty)
  | DUserTy (x, ty) -> DUserTy (x, replace_ty ty)
  (* partitioning *)
  | DPartition e -> DPartition (replace_exp e)
  | DInterface e -> DInterface (replace_exp e)
  | _ -> failwith "not yet implemented!"
;;

(** Functions to convert a solution to the replaced version to a solution
    to the original version **)

let rec unreplace_value v oldty =
  let open Syntax in
  let unreplaced_v =
    match v.v, oldty with
    | VUnit, TUnit
    | VBool _, TBool
    | VInt _, TInt _ -> v
    | VTuple tys, TTuple oldtys -> vtuple (List.map2 unreplace_value tys oldtys)
    | VUnit, TTuple [] -> vtuple []
    | _, TTuple [ty] -> vtuple [unreplace_value v ty]
    | VOption vo, TOption ty -> voption (mapo (fun vo -> unreplace_value vo ty) vo)
    | VRecord _, _ | VMap _, _ | VClosure _, _ -> failwith "Should be unrolled"
    | _ -> failwith @@ Printf.sprintf "Type and value do not match: (%s, %s)"
        (Printing.value_to_string v) (Printing.ty_to_string oldty)
  in
  avalue (unreplaced_v, Some oldty, v.vspan)
;;

let map_back_symbolics decls (sol : Nv_solution.Solution.t) =
  let symbolics = Syntax.get_symbolics decls in
  let symbolics_to_convert =
    BatList.filter_map
      (fun (v, e) ->
         let oldty = match e with Syntax.Ty ty -> ty | Exp e -> Nv_utils.OCamlUtils.oget e.ety in
         let newty = replace_ty oldty in
         if Typing.equiv_tys oldty newty then None
         else Some (v, oldty))
      symbolics
  in
  let convert_symbolic var v =
    let symb =
      List.find_opt
        (fun (var', _) -> Nv_datastructures.Var.equal var var')
        symbolics_to_convert
    in
    match symb with
    | None -> v
    | Some(_, original_ty) ->
      unreplace_value v original_ty
  in
  let new_symbolics =
    Collections.VarMap.mapi convert_symbolic sol.symbolics
  in
  new_symbolics

let map_back_attrs decls (sol : Nv_solution.Solution.t) =
  let attr_ty = Nv_utils.OCamlUtils.oget (Syntax.get_attr_type decls) in
  let unrolled_attr_ty = replace_ty attr_ty in
  if Typing.equiv_tys attr_ty unrolled_attr_ty then sol.labels
  else (* Attribute type involved a map, so transform all attributes *)
    Nv_datastructures.AdjGraph.VertexMap.map
      (fun v -> unreplace_value v attr_ty)
      sol.labels
;;

let map_back decls (sol : Nv_solution.Solution.t) =
  {sol with
   symbolics = map_back_symbolics decls sol;
   labels = map_back_attrs decls sol}
;;

let replace_declarations decls =
  (List.map replace_decl decls, map_back decls)
