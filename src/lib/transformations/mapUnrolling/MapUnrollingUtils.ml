open Nv_lang
open Syntax
open Collections
open Nv_datastructures

type maplist = (Syntax.ty * (ExpSet.t * VarSet.t)) list;;

let maplist_to_string (lst : maplist) =
  let entry_to_string (ty, (const_keys, symb_keys)) =
    Printf.sprintf "(%s, [%s], [%s])" (Printing.ty_to_string ty)
      (ExpSet.fold
         (fun e s -> s ^ Printing.exp_to_string e ^ "; ")
         const_keys "")
      (VarSet.fold
         (fun v s -> s ^ Nv_datastructures.Var.to_string v ^ "; ")
         symb_keys "")
  in
  Printf.sprintf "[%s]"
    (BatString.concat ";" @@
     BatList.map entry_to_string lst)
;;

let add_key mty symbolics (const_keys, symb_keys) keyo =
  match keyo with
  | None -> const_keys, symb_keys
  | Some ({e=EVar var}) when BatList.mem_cmp Nv_datastructures.Var.compare var symbolics ->
    const_keys, (VarSet.add var symb_keys)
  | Some key ->
    if is_value key then ExpSet.add key const_keys, symb_keys
    else
      match mty with
      | TMap (TNode, _)
      | TMap (TEdge, _) ->
        const_keys, symb_keys
      | _ ->
        failwith @@
        "Encountered non-variable, non constant map key whose type isn't node or edge: "
        ^ Printing.exp_to_string key
;;

let rec add_to_maplist symbolics (ty, keyo) lst : maplist =
  let add_key = add_key ty symbolics in
  match lst with
  | [] -> [(ty, add_key (ExpSet.empty, VarSet.empty) keyo)]
  | (ty2, keys) :: tl ->
    if Syntax.equal_tys ty ty2 then
      (ty, add_key keys keyo) :: tl
    else
      (ty2, keys) :: add_to_maplist symbolics (ty, keyo) tl
;;

let add_if_map_type symbolics (ty, keyo) lst : maplist =
  match Typing.canonicalize_type ty with
  | TMap (ty1, ty2) ->
    add_to_maplist symbolics (TMap (ty1, ty2), keyo) lst
  | _ -> lst
;;

let rec collect_in_exp (symbolics : var list) (exp : Syntax.exp) (acc : maplist) : maplist =
  (* print_endline @@ "Collecting in expr " ^ Printing.exp_to_string exp; *)
  let curr_ty = Nv_utils.OCamlUtils.oget exp.ety in
  let collect_in_exp = collect_in_exp symbolics in
  let add_if_map_type = add_if_map_type symbolics in
  (* If our current expression has map type, add that to our list *)
  let acc = add_if_map_type (curr_ty, None) acc in
  match exp.e with
  | EVar _
  | EVal _ -> acc
  | EOp (op, es) ->
    begin
      (* Collect key if necessary *)
      let acc =
        match op, es with
        | MGet, [m; key]
        | MSet, [m; key; _] ->
          add_if_map_type ((Nv_utils.OCamlUtils.oget m.ety), Some key) acc
        | _ -> acc
      in
      BatList.fold_left (BatPervasives.flip collect_in_exp) acc es
    end
  | EFun f ->
    collect_in_exp f.body acc
  | ELet (_, e1, e2)
  | EApp (e1, e2) ->
    acc
    |> collect_in_exp e1
    |> collect_in_exp e2
  | EIf (e1, e2, e3) ->
    acc
    |> collect_in_exp e1
    |> collect_in_exp e2
    |> collect_in_exp e3
  | ETuple es ->
    BatList.fold_left (BatPervasives.flip collect_in_exp) acc es
  | ERecord map ->
    StringMap.fold (fun _ -> collect_in_exp) map acc
  | EProject _ -> failwith ""
  | ESome e ->
    collect_in_exp e acc
  | EMatch (e, branches) ->
    let acc = collect_in_exp e acc in
    foldBranches (fun (_,e) acc -> collect_in_exp e acc)
      acc branches
  | ETy (e, _) ->
    collect_in_exp e acc
;;

let collect_in_decl (symbolics : var list) (d : declaration) (acc : maplist) : maplist =
  (* print_endline @@ "Collecting in decl " ^ Printing.declaration_to_string d; *)
  let add_if_map_type = add_if_map_type symbolics in
  let collect_in_exp = collect_in_exp symbolics in
  match d with
  | DLet (_, tyo, exp) ->
    add_if_map_type (Nv_utils.OCamlUtils.oget tyo, None) acc
    |> collect_in_exp exp
  | DSymbolic (_, toe) ->
    begin
      match toe with
      | Ty ty ->
        add_if_map_type (ty, None) acc
      | Exp exp -> collect_in_exp exp acc
    end
  | DATy ty ->
    add_if_map_type (ty, None) acc
  | DUserTy (_, ty) ->
    add_if_map_type (ty, None) acc
  | DMerge exp
  | DTrans exp
  | DInit exp
  | DAssert exp
  | DPartition exp (* partitioning *)
  | DInterface exp (* partitioning *)
  | DRequire exp ->
    collect_in_exp exp acc
  | DNodes _
  | DEdges _ ->
    acc
;;

let lookup_map_type ty lst =
  BatList.assoc ty lst

(*
  In order to make sure fold works properly, we require that when we unroll
  maps whose keys are nodes or edges, we use all possible values for the keys,
  instead of just the values which appear in the program
*)
let add_keys_for_nodes_and_edges decls maplist =
  let nodes =
    get_nodes decls
    |> Nv_utils.OCamlUtils.oget
    |> BatEnum.(--^) 0 (* Enum of 0 to (num_nodes - 1) *)
    |> BatEnum.map (fun n -> e_val (vnode n))
    |> ExpSet.of_enum
  in
  let edges =
    get_edges decls
    |> Nv_utils.OCamlUtils.oget
    |> List.map (fun (n1, n2) -> e_val (vedge (n1, n2)))
    |> ExpSet.of_list
  in
  List.map
    (fun (mapty, (const_keys, symb_keys)) ->
       match mapty with
       | TMap (TNode, _) -> mapty, (nodes, symb_keys)
       | TMap (TEdge, _) -> mapty, (edges, symb_keys)
       | _ -> mapty, (const_keys, symb_keys)
    ) maplist
;;

(* Given a program on which type inference has been run, goes through
   it and returns a list of each map type which appears in that program,
   combined with the set of keys used for that map type. *)
let collect_map_types_and_keys (decls : declarations) : maplist =
  let symbolics = List.map fst (get_symbolics decls) in
  BatList.fold_left (BatPervasives.flip (collect_in_decl symbolics)) [] decls
  |> add_keys_for_nodes_and_edges decls
