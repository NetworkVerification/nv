open Collections
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

let rec check_closure info (x: VarSet.t) (e: exp) =
  match e.e with
  | EVar v ->
    if VarSet.mem v x then ()
    else
      let msg =
        Printf.sprintf
          "captured variable: %s not allowed in mapIf closure"
          (Var.name v)
      in
      Console.error_position info e.espan msg
  | EVal v -> ()
  | EOp (op, es) ->
    ( match op with
      | And | Or | Not | UEq | UAdd _ | ULess _ | ULeq _ | USub _ -> ()
      | _ ->
        let msg =
          Printf.sprintf
            "unsupported operation %s in mapIf closure"
            (Printing.op_to_string op)
        in
        Console.error_position info e.espan msg ) ;
    List.iter (check_closure info x) es
  | EFun _ ->
    Console.error_position info e.espan
      "function not allowed in mapIf closure"
  | EApp (e1, e2) ->
    Console.error_position info e.espan
      "function application allowed in mapIf closure"
  | EIf (e1, e2, e3) ->
    check_closure info x e1 ;
    check_closure info x e2 ;
    check_closure info x e3
  | ELet (y, e1, e2) ->
    let set = VarSet.add y x in
    check_closure info set e1 ;
    check_closure info set e2
  | ETuple es -> List.iter (check_closure info x) es
  | ESome e -> check_closure info x e
  | EMatch (e, bs) ->
    check_closure info x e ;
    List.iter
      (fun (p, e) ->
         let set = pattern_vars p in
         check_closure info (VarSet.union set x) e )
      bs
  | ETy (e, _) -> check_closure info x e

and pattern_vars (p: pattern) =
  match p with
  | PWild | PBool _ | PInt _ | POption None -> VarSet.empty
  | PVar v -> VarSet.singleton v
  | PTuple ps ->
    List.fold_left
      (fun acc p -> VarSet.union acc (pattern_vars p))
      VarSet.empty ps
  | POption (Some p) -> pattern_vars p

let check_closures info _ (e: exp) =
  match e.e with
  | EOp (MMapFilter, [e1; e2; e3]) -> (
      match e1.e with
      | EFun {arg= x; body= be} ->
        check_closure info (VarSet.singleton x) be
      | _ ->
        let msg =
          "first parameter to mapIf must be an immediate function"
        in
        Console.error_position info e1.espan msg )
  | _ -> ()

let rec is_literal (exp : Syntax.exp) : bool =
  match exp.e with
  | EVar _
  | EOp _
  | EFun _
  | EApp _
  | EIf _
  | ELet _
  | EMatch _ ->
    false
  | ESome exp2 ->
    is_literal exp2
  | ETuple es ->
    List.fold_left (fun b exp -> b && is_literal exp) true es
  | EVal _ -> true
  | ETy (exp2, _) -> is_literal exp2

(* Verify that the only map keys used are literals *)
let check_keys info _ (e : exp) =
  match e.e with
  | EOp (MGet, [_; k])
  | EOp (MSet, [_; k; _]) ->
    if not (is_literal k) then
      let msg =
        "Only literals may be used as keys into a map"
      in
      Console.error_position info k.espan msg
  | _ -> ()

let check info (ds: declarations) : unit =
  Visitors.iter_exp_decls (check_types info) ds ;
  Visitors.iter_exp_decls (check_closures info) ds ;
  Visitors.iter_exp_decls (check_keys info) ds
