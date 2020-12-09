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

let of_decls d = Decls d

type transform_result =
  | Network of declaration
  (* Solution: return Solve, Symbolics, Asserts, and two groups of Requires *)
  | Solution of
      (declaration
      * declaration list
      * declaration list
      * declaration list
      * declaration list)
  | Property of declaration
  | None

(* Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 * that need to be added with it. *)
let transform_declaration parted_srp decl : transform_result =
  let ({ nodes; edges; rank; _ } : partitioned_srp) = parted_srp in
  match decl with
  | DNodes _ -> Network (DNodes nodes)
  | DEdges _ -> Network (DEdges edges)
  | DSolve s ->
    let solve', assert', symbolics, reqs = transform_solve s parted_srp in
    let sort_hyp exp r (lt, gt) =
      if r < rank then DRequire exp :: lt, gt else lt, DRequire exp :: gt
    in
    let lesser_req_decls, greater_req_decls = Map.foldi sort_hyp reqs ([], []) in
    Solution
      ( DSolve solve'
      , List.map (fun (v, t) -> DSymbolic (v, t)) symbolics
      , List.map (fun e -> DAssert e) assert'
      , lesser_req_decls
      , greater_req_decls )
  | DPartition _ -> None
  | DAssert e -> Property (DAssert (transform_assert e parted_srp))
  | _ -> Network decl
;;

let transform_declarations decls parted_srp =
  let transformed_decls = List.map (transform_declaration parted_srp) decls in
  (* divide up the declarations as appropriate *)
  let rec split_decls (net, guar, hyps, lt_hyp, gt_hyp, prop) l =
    match l with
    | [] -> net, guar, hyps, lt_hyp, gt_hyp, prop
    | h :: t ->
      begin
        match h with
        | Network d -> split_decls (d :: net, guar, hyps, lt_hyp, gt_hyp, prop) t
        | Solution (d, s, g, lh, gh) ->
          split_decls (d :: net, g @ guar, s @ hyps, lh @ lt_hyp, gh @ gt_hyp, prop) t
        | Property p -> split_decls (net, guar, hyps, lt_hyp, gt_hyp, p :: prop) t
        | None -> split_decls (net, guar, hyps, lt_hyp, gt_hyp, prop) t
      end
  in
  let base, guar, hyps, lth, gth, prop = split_decls ([], [], [], [], [], []) transformed_decls in
  { base; prop; guar; hyps; lth; gth }
;;

let lift (f : declarations -> declarations) decls =
  { lth = f decls.lth
  ; gth = f decls.gth
  ; hyps = f decls.hyps
  ; guar = f decls.guar
  ; prop = f decls.prop
  ; base = f decls.base
  }
;;

let lift_mb (f : declarations -> declarations * Nv_solution.Solution.map_back) decls =
  let lth, _lhf = f decls.lth in
  let gth, _ghf = f decls.gth in
  let hyps, _hf = f decls.hyps in
  let guar, _gf = f decls.guar in
  let prop, _pf = f decls.prop in
  let base, f = f decls.base in
  { lth; gth; hyps; guar; prop; base }, f
;;
