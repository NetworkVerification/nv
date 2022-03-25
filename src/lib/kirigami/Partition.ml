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

(* Collect all variables from symbolics associated with each input of the partitioned_srp.
 * Implicitly assumes that variable names can be checked to determine the original variable
 * after performing transformations. *)
let update_vars_from_symbolics partitioned_srp (symbs : (var * ty_or_exp) list) =
  let get_edge_symbs edge =
    List.filter_map
      (fun (v, _) -> if SrpRemapping.is_hyp_var edge v then Some v else None)
      symbs
  in
  { partitioned_srp with
    inputs =
      VertexMap.map
        (fun ies ->
          List.map
            (fun (ie : input_exp) -> { ie with var_names = get_edge_symbs ie.edge })
            ies)
        partitioned_srp.inputs
  }
;;

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
let transform_declaration parted_srp decl : declaration option =
  let ({ nodes; edges; _ } : partitioned_srp) = parted_srp in
  (* get the list of all assumption symbolics which should appear *)
  let valid_edges = get_cross_edges parted_srp in
  match decl with
  | DNodes _ -> Some (DNodes nodes)
  | DEdges _ -> Some (DEdges edges)
  (* drop any hypotheses that don't belong to this partition *)
  | DSymbolic (v, _) ->
    (match (SrpRemapping.var_to_edge v) with
    | Some e when not (List.exists ((=) e) valid_edges) -> None
    | _ -> Some decl)
  | DPartition _ -> None
  | DAssert e -> Some (DAssert (transform_assert e parted_srp))
  | _ -> Some decl
;;

let transform_declarations decls parted_srp =
  let symbs = get_symbolics decls in
  let parted_srp = update_vars_from_symbolics parted_srp symbs in
  let add_new_decl (part, decls) d =
    match transform_declaration part d with
    | Some d -> part, d :: decls
    | None -> part, decls
  in
  List.fold_left add_new_decl (parted_srp, []) decls
;;
