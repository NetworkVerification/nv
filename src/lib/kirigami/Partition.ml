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
  (* TODO: see if we can drop this!
   * currently has an issue in renaming with an unbound solution variable when we do *)
  | Property of declaration
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
    (List.map (fun ie -> ie.var) input_exps) @ l
  in
  VertexMap.fold get_vars parted_srp.inputs []

(* Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 * that need to be added with it. *)
let transform_declaration parted_srp decl : transform_result =
  let ({ nodes; edges; _ } : partitioned_srp) = parted_srp in
  let valid_hyps = valid_hyps parted_srp in
  match decl with
  | DNodes _ -> Network (DNodes nodes)
  | DEdges _ -> Network (DEdges edges)
  (* drop any hypotheses that don't belong to this partition *)
  | DSymbolic (v, _) ->
    (* print_endline (Var.name v);
     * print_endline (Nv_utils.OCamlUtils.list_to_string Var.name valid_hyps); *)
    (* get the original variable form in case it's been projected *)
    let v = snd (unproj_var v) in
    if (String.starts_with (Var.name v) "hyp" && not (List.mem v valid_hyps))
    then None
    else Network decl
  | DSolve s ->
    let part', solve' = transform_solve s parted_srp in
    (* let sort_hyp exp r (lt, gt) =
     *   if r < rank then DRequire exp :: lt, gt else lt, DRequire exp :: gt
     * in *)
    (* let lesser_req_decls, greater_req_decls = Map.foldi sort_hyp reqs ([], []) in *)
    Solution (DSolve solve', part')
    (* Solution
     *   ( DSolve solve'
     *   , List.map (fun (v, t) -> DSymbolic (v, t)) symbolics
     *   , List.map (fun e -> DAssert e) assert'
     *   , lesser_req_decls
     *   , greater_req_decls ) *)
  | DPartition _ -> None
  | DAssert e -> Property (DAssert (transform_assert e parted_srp))
  | _ -> Network decl
;;

let transform_declarations decls parted_srp =
  let transformed_decls = List.map (transform_declaration parted_srp) decls in
  (* divide up the declarations as appropriate *)
  let rec split_decls (net, prop, part) l =
    match l with
    | [] -> net, prop, part
    | h :: t ->
      begin
        match h with
        | Network d -> split_decls (d :: net, prop, part) t
        | Solution (d, p) ->
          split_decls (d :: net, prop, p) t
        | Property p -> split_decls (net, p :: prop, part) t
        | None -> split_decls (net, prop, part) t
      end
  in
  let base, prop, part = split_decls ([], [], parted_srp) transformed_decls in
  (* FIXME: this leads to issues if there are multiple solves *)
  part, { base; prop; guar = []; hyps = []; lth = []; gth = [] }
;;
