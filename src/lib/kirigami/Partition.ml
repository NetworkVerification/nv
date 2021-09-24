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
  | Solution of (partitioned_srp * declaration)
  | None

(** Return a new set of declarations of all symbolics added by this partition. *)
let get_hyp_symbolics part =
  VertexMap.fold
    (fun _ input_exps ds ->
      List.fold_left
        (fun ds ie -> List.map (fun (v, t) -> DSymbolic (v, Ty t)) ie.var @ ds)
        ds
        input_exps)
    part.inputs
    []
;;

(* let valid_hyps parted_srp =
 *   (\* the "symbolic-" prefix is added by RenameForSMT *\)
 *   let get_vars _ input_exps l =
 *     List.map (fun ie -> "symbolic-" ^ Var.name ie.var) input_exps @ l
 *   in
 *   VertexMap.fold get_vars parted_srp.inputs []
 * ;; *)

(** Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 ** that need to be added with it.
 ** NOTE: must run after Nv_transformations.RenameForSMT.rename_declarations in order to match symbolics
 ** correctly. *)
let transform_declaration parted_srp decl : transform_result =
  let ({ nodes; edges; _ } : partitioned_srp) = parted_srp in
  (* let valid_hyps = valid_hyps parted_srp in *)
  match decl with
  | DNodes _ -> Network (DNodes nodes)
  | DEdges _ ->
    Network (DEdges edges)
    (* drop any hypotheses that don't belong to this partition *)
    (* | DSymbolic (v, _) -> *)
    (* print_endline (Var.name v);
     * print_endline (Nv_utils.OCamlUtils.list_to_string (fun s -> s) valid_hyps); *)
    (* get the original variable form in case it's been projected *)
    (* let v = snd (unproj_var v) in
     * if String.starts_with (Var.name v) "symbolic-hyp"
     *    && not (List.mem (Var.name v) valid_hyps)
     * then None
     * else Network decl *)
  | DSolve s ->
    let part', solve' = transform_solve s parted_srp in
    Solution (part', DSolve solve')
  | DPartition _ -> None
  | DAssert e -> Network (DAssert (transform_assert e parted_srp))
  | _ -> Network decl
;;

let transform_declarations decls parted_srp =
  let add_new_decl (part, decls) d =
    match transform_declaration part d with
    | Network d -> part, d :: decls
    | Solution (p, d) -> p, d :: decls
    | None -> part, decls
  in
  let p, ds = List.fold_left add_new_decl (parted_srp, []) decls in
  p, get_hyp_symbolics p @ ds
;;
