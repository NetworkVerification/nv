open Batteries
open Nv_lang
open Syntax

(* Unroll all map types contained in decls. Cannot handle polymorphism,
 * so requires that inlining has been run first.
 *
 * Requires the user provide a maplist.
 * For the default maplist, see *unroll*, below. *)
let unroll_with_maplist _ ~(maplist : MapUnrollingUtils.maplist) decls =
  let unrolled_decls, map_back1 =
    BatList.fold_left
      (fun (decls, f) (mty, keys) ->
        let const_keys = Collections.ExpSet.elements (fst keys) in
        let symb_keys = Collections.VarSet.elements (snd keys) in
        let new_decls, f' =
          MapUnrollingSingle.unroll_declarations mty (const_keys, symb_keys) decls
        in
        new_decls, fun x -> f (f' x))
      (decls, fun x -> x)
      maplist
  in
  let final_decls, map_back2 = CleanupTuples.cleanup_declarations unrolled_decls in
  final_decls, map_back1 % map_back2
;;

(* Unroll all map types contained in decls. Cannot handle polymorphism,
   so requires that inlining has been run first.

   Returns an equivalent set of decls where all map types have been
   replaced with tuple types, and a function which converts a Solution
   to the new decls into a solution for the old decls. *)
let unroll_decls info decls =
  let maplist = MapUnrollingUtils.collect_map_types_and_keys decls in
  unroll_with_maplist info ~maplist decls
;;

let unroll_groups info (dgs : declaration_groups) =
  let maplist = MapUnrollingUtils.collect_map_types_and_keys (dgs.hyps @ dgs.base) in
  let hyps, hf = unroll_with_maplist info ~maplist dgs.hyps in
  let base, f = unroll_with_maplist info ~maplist dgs.base in
  let prop, _ = unroll_with_maplist info ~maplist dgs.prop in
  let guar, _ = unroll_with_maplist info ~maplist dgs.guar in
  let lth, _ = unroll_with_maplist info ~maplist dgs.lth in
  let gth, _ = unroll_with_maplist info ~maplist dgs.gth in
  { base; prop; guar; hyps; lth; gth }, f % hf
;;

let unroll info d_or_g =
  match d_or_g with
  | Decls d ->
    let d, f = unroll_decls info d in
    Decls d, f
  | Grp g ->
    let g, f = unroll_groups info g in
    Grp g, f
;;
