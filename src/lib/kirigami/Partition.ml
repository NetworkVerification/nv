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

(** Return a new set of declarations of all symbolics added by partitions. *)
let get_hyp_symbolics ty partitions =
  let add_partition_hyps l part =
    VertexMap.fold
      (fun _ input_exps l ->
        List.map (fun ie -> DSymbolic (ie.var, Ty ty)) input_exps @ l)
      part.inputs
      l
  in
  List.fold_left add_partition_hyps [] partitions
;;

let valid_hyps parted_srp =
  let get_vars _ input_exps l =
    List.map (fun ie -> "symbolic-" ^ Var.name ie.var) input_exps @ l
  in
  VertexMap.fold get_vars parted_srp.inputs []
;;

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
    if String.starts_with (Var.name v) "symbolic-hyp"
       && not (List.mem (Var.name v) valid_hyps)
    then None
    else Network decl
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
  List.fold_left add_new_decl (parted_srp, []) decls
;;

let transform_declaration_inverted decl fragments : declaration option list =
  (* TODO: visit the declarations and copy them to each fragment; *)
  match decl with
  | DNodes _ -> (List.map (fun p -> Some (DNodes p.nodes)) fragments)
  | DEdges _ -> (List.map (fun p -> Some (DEdges p.edges)) fragments)
  | DSymbolic (v, _) ->
    let v = snd (unproj_var v) in
    let filter_hyp p : declaration option =
      let accepted = valid_hyps p in
      if String.starts_with (Var.name v) "symbolic-hyp" && not (List.mem (Var.name v) accepted) then None else Some decl
    in
    List.map filter_hyp fragments
  | DSolve _s -> (* for each fragment, remap the expressions appropriately *) failwith "todo"
  | DPartition _ -> List.make (List.length fragments) (None:declaration option)
  | DAssert _e -> (* for each fragment, trim the appropriate number of conjuncts *) failwith "todo"
  | _ -> (List.make (List.length fragments) (Some decl))
;;

let transform_declarations_inverted decls fragments : declarations list =
  (* use transpose to connect the declarations for each fragment *)
  let fragment_decls = List.transpose (List.map (fun d -> transform_declaration_inverted d fragments) decls) in
  (* filter out Nones in declarations *)
  List.map (List.filter_map identity) fragment_decls
;;
