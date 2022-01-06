open Nv_lang
open Nv_datastructures
open Nv_utils
open Collections
open Syntax
open Batteries

(* Check a variety of other requirements for a well-
   formed program. Assumes the program is well-typed *)

let rec has_map ty =
  match get_inner_type ty with
  | TUnit | TBool | TInt _ | TNode | TEdge | TVar _ | QVar _ -> false
  | TTuple ts -> List.exists has_map ts
  | TArrow (ty1, ty2) -> has_map ty1 || has_map ty2
  | TOption ty -> has_map ty
  | TRecord map -> StringMap.exists (fun _ -> has_map) map
  | TMap _ -> true
;;

let rec check_type ty : bool =
  match get_inner_type ty with
  | TUnit | TBool | TInt _ | TNode | TEdge | TVar _ | QVar _ -> true
  | TTuple ts -> List.for_all check_type ts
  | TOption ty -> check_type ty
  | TArrow (ty1, ty2) -> check_type ty1 && check_type ty2
  | TRecord map -> StringMap.for_all (fun _ -> check_type) map
  | TMap (kty, vty) -> (not (has_map kty)) && check_type kty && check_type vty
;;

let check_types info _ (e : exp) =
  let ty = Nv_utils.OCamlUtils.oget e.ety in
  if not (check_type ty)
  then (
    let msg = "expression type has dictionary type with dictionary keys" in
    Console.error_position info e.espan msg)
;;

let rec check_closure info (x : VarSet.t) (e : exp) =
  match e.e with
  | EVar v ->
    if VarSet.mem v x
    then ()
    else (
      let msg =
        Printf.sprintf "captured variable: %s not allowed in mapIf closure" (Var.name v)
      in
      Console.error_position info e.espan msg)
  | EVal _ -> ()
  | EOp (op, es) ->
    (match op with
    | And | Or | Not | Eq | UAdd _ | ULess _ | ULeq _ | USub _ | NLess | NLeq -> ()
    | _ ->
      let msg =
        Printf.sprintf
          "unsupported operation %s in mapIf closure"
          (Printing.op_to_string op)
      in
      Console.error_position info e.espan msg);
    List.iter (check_closure info x) es
  | EFun _ ->
    (* Console.error_position info e.espan *)
    (* "function not allowed in mapIf closure" *)
    ()
  | EApp (_, _) ->
    (* Console.error_position info e.espan *)
    (* "function application allowed in mapIf closure" *)
    ()
  | EIf (e1, e2, e3) ->
    check_closure info x e1;
    check_closure info x e2;
    check_closure info x e3
  | ELet (y, e1, e2) ->
    let set = VarSet.add y x in
    check_closure info set e1;
    check_closure info set e2
  | ETuple es -> List.iter (check_closure info x) es
  | ERecord map -> StringMap.iter (fun _ -> check_closure info x) map
  | EProject (e, _) -> check_closure info x e
  | ESome e -> check_closure info x e
  | EMatch (e, bs) ->
    check_closure info x e;
    iterBranches
      (fun (p, e) ->
        let set = pattern_vars p in
        check_closure info (VarSet.union set x) e)
      bs
  | ETy (e, _) -> check_closure info x e

and pattern_vars (p : pattern) =
  match p with
  | PWild | PUnit | PBool _ | PInt _ | PNode _ | POption None -> VarSet.empty
  | PVar v -> VarSet.singleton v
  | PEdge (p1, p2) -> VarSet.union (pattern_vars p1) (pattern_vars p2)
  | PTuple ps ->
    List.fold_left (fun acc p -> VarSet.union acc (pattern_vars p)) VarSet.empty ps
  | PRecord pmap ->
    StringMap.fold (fun _ p acc -> VarSet.union acc (pattern_vars p)) pmap VarSet.empty
  | POption (Some p) -> pattern_vars p
;;

let check_closures info _ (e : exp) =
  match e.e with
  | EOp (MMapFilter, [e1; _; _]) ->
    (match e1.e with
    | EFun { arg = x; body = be } -> check_closure info (VarSet.singleton x) be
    | _ ->
      let msg = "first parameter to mapIf must be an immediate function" in
      Console.error_position info e1.espan msg)
  | _ -> ()
;;

(* Checks that no label appears more than once in
   record declarations *)
let check_record_label_uniqueness info decls =
  (* Check if a sorted list has duplicate elements *)
  let rec find_dup lst =
    match lst with
    | [] | [_] -> None
    | x1 :: x2 :: tl -> if String.equal x1 x2 then Some x1 else find_dup (x2 :: tl)
  in
  let all_labels =
    get_record_types decls
    |> List.unique ~eq:(StringMap.equal Typing.equiv_tys)
    (* Filter out record type aliasing *)
    |> List.map (fun map -> BatList.of_enum @@ StringMap.keys map)
    |> List.concat
  in
  let sorted = List.sort String.compare all_labels in
  match find_dup sorted with
  | None -> ()
  | Some name ->
    let msg = Printf.sprintf "Record label %s appears more than once!" name in
    Console.error_position info Span.default msg
;;

(* let rec is_literal (exp : Syntax.exp) : bool =
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
    List.for_all is_literal es
   | EVal _ -> true
   | ETy (exp2, _) -> is_literal exp2
   | ERecord map -> StringMap.for_all (fun _ -> is_literal) map
   | EProject (exp2, _) -> is_literal exp2

   (* Verify that the only map keys used are literals *)
   let check_keys info _ (e : exp) =
   match e.e with
   (* | EOp (MGet, [_; k]) *)
   | EOp (MSet, [_; k; _]) ->
    if not (is_literal k) then
      let msg =
        "Only literals may be used as keys into a map"
      in
      Console.error_position info k.espan msg
   | _ -> () *)

(* Ensures every node/edge value in the program actually exists in the network *)
let check_nodes_and_edges info num_nodes edges _ (e : exp) =
  match e.e with
  | EVal v ->
    begin
      match v.v with
      | VNode n ->
        if n < num_nodes
        then ()
        else (
          let msg =
            Printf.sprintf
              "Node %d does not appear in the network! (The highest node value is %d)"
              n
              (num_nodes - 1)
          in
          Console.error_position info v.vspan msg)
      | VEdge (n1, n2) ->
        if List.mem (n1, n2) edges
        then ()
        else (
          let msg = Printf.sprintf "Edge %d~%d does not appear in the network!" n1 n2 in
          Console.error_position info v.vspan msg)
      | _ -> ()
    end
  | _ -> ()
;;

let check_valid_edges num_nodes edges =
  let check_edge (u, v) =
    if u < num_nodes && v < num_nodes
    then ()
    else (
      let msg =
        Printf.sprintf
          "Edge %d~%d is invalid! (The highest node value is %d)"
          u
          v
          num_nodes
      in
      Console.error msg)
  in
  List.iter check_edge edges
;;

let check info (ds : declarations) : unit =
  check_record_label_uniqueness info ds;
  Visitors.iter_exp_decls (check_types info) ds;
  (* Visitors.iter_exp_decls (check_closures info) ds ; *)
  (* Is this still necessary? *)
  (* Visitors.iter_exp_decls (check_keys info) ds; *)
  let nodes = get_nodes ds |> Option.get in
  let edges = get_edges ds |> Option.get in
  check_valid_edges nodes edges;
  Visitors.iter_exp_decls (check_nodes_and_edges info nodes edges) ds;
  ()
;;
