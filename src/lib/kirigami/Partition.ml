open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Nv_utils.PrimitiveCollections
open Nv_lang
open Nv_lang.Syntax
open Nv_lang.Collections
open TransformDecls
open Nv_interpreter
open Nv_utils.OCamlUtils
open SrpRemapping

type transform_result =
  | Decl of declaration
  (* Solution: return Solve and updated partitioned SRP *)
  | UpdateDecl of (partitioned_srp * declaration)
  | Drop

(** Return a new set of declarations of all symbolics added by this partition. *)
let get_hyp_symbolics aty (part : partitioned_srp) =
  VertexMap.fold
    (fun _ input_exps ds ->
      List.fold_left
        (fun ds (ie : input_exp) ->
          List.map (fun v -> DSymbolic (v, Ty aty)) ie.var_names @ ds)
        ds
        input_exps)
    part.inputs
    []
;;

(** Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 ** that need to be added with it.
 ** NOTE: must run after Nv_transformations.RenameForSMT.rename_declarations in order to match symbolics
 ** correctly. *)
let transform_declaration parted_srp decl : transform_result =
  let ({ nodes; edges; _ } : partitioned_srp) = parted_srp in
  (* get the list of all assumption symbolics which should appear *)
  let valid_edges = get_cross_edges parted_srp in
  match decl with
  | DNodes _ -> Decl (DNodes nodes)
  | DEdges _ -> Decl (DEdges edges)
  (* drop any hypotheses that don't belong to this partition *)
  | DSymbolic (v, _) ->
    (* print_endline (Var.name v); *)
    (* print_endline (Nv_utils.OCamlUtils.list_to_string (fun s -> s) valid_hyps); *)
    (match (SrpRemapping.var_to_edge v) with
    | Some e when not (List.exists ((=) e) valid_edges) -> Drop
    | _ -> Decl decl)
  | DSolve s ->
    let part', solve' = transform_solve s parted_srp in
    UpdateDecl (part', DSolve solve')
  | DPartition _ -> Drop
  | DAssert e -> Decl (DAssert (transform_assert e parted_srp))
  | _ -> Decl decl
;;

let transform_declarations decls parted_srp =
  let symbs = get_symbolics decls in
  let parted_srp = TransformDecls.update_vars_from_symbolics parted_srp symbs in
  let add_new_decl (part, decls) d =
    match transform_declaration part d with
    | Decl d -> part, d :: decls
    | UpdateDecl (p, d) -> p, d :: decls
    | Drop -> part, decls
  in
  List.fold_left add_new_decl (parted_srp, []) decls
;;
