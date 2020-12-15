open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Nv_utils.PrimitiveCollections
open Nv_lang
open Nv_lang.Syntax
open TransformDecls
open Nv_interpreter
open Nv_utils.OCamlUtils
open SrpRemapping

type transform_result =
  | Network of declaration
  (* Solution: return Solve and updated partitioned SRP *)
  | Solution of (declaration * partitioned_srp)
  | None

(** Return a new set of declarations of all symbolics added by partitions. *)
let get_hyp_symbolics ty partitions =
  let add_partition_hyps l part =
    VertexMap.fold
      (fun _ input_exps l -> (List.map (fun ie -> DSymbolic (ie.var, Ty ty)) input_exps) @ l)
      part.inputs
      l
  in
  List.fold_left add_partition_hyps [] partitions

let valid_hyps parted_srp =
  let get_vars _ input_exps l =
    (List.map (fun ie -> "symbolic-" ^ Var.name ie.var) input_exps) @ l
  in
  VertexMap.fold get_vars parted_srp.inputs []

(** Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 ** that need to be added with it. *)
let transform_declaration parted_srp decl : transform_result =
  let ({ nodes; edges; _ } : partitioned_srp) = parted_srp in
  let valid_hyps = valid_hyps parted_srp in
  match decl with
  | DNodes _ -> Network (DNodes nodes)
  | DEdges _ -> Network (DEdges edges)
  (* drop any hypotheses that don't belong to this partition *)
  | DSymbolic (v, _) ->
    (* print_endline (Var.name v);
     * print_endline (Nv_utils.OCamlUtils.list_to_string (fun s -> s) valid_hyps); *)
    (* get the original variable form in case it's been projected *)
    let v = snd (unproj_var v) in
    if (String.starts_with (Var.name v) "symbolic-hyp" && not (List.mem (Var.name v) valid_hyps))
    then None
    else Network decl
  | DSolve s ->
    let part', solve' = transform_solve s parted_srp in
    Solution (DSolve solve', part')
  | DPartition _ -> None
  | DAssert e -> Network (DAssert (transform_assert e parted_srp))
  | _ -> Network decl
;;

let transform_declarations decls parted_srp =
  let transformed_decls = List.map (transform_declaration parted_srp) decls in
  (* divide up the declarations as appropriate *)
  let rec split_decls (net, part) l =
    match l with
    | [] -> net, part
    | h :: t ->
      (match h with
      | Network d -> split_decls (d :: net, part) t
      | Solution (d, p) -> split_decls (d :: net, p) t
      | None -> split_decls (net, part) t)
  in
  let decls, part = split_decls ([], parted_srp) transformed_decls in
  (* FIXME: this leads to issues if there are multiple solves *)
  part, decls
;;
