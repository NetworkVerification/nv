open Batteries
open Nv_lang

(* Unroll all map types contained in decls. Cannot handle polymorphism,
   so requires that inlining has been run first.

   Returns an equivalent set of decls where all map types have been
   replaced with tuple types, and a function which converts a Solution
   to the new decls into a solution for the old decls. *)
let unroll _ decls =
  let maplist = MapUnrollingUtils.collect_map_types_and_keys decls in
  let unrolled_decls, map_back1 =
    BatList.fold_left
      (fun (decls, f) (mty, keys) ->
        let const_keys = Collections.ExpSet.elements (fst keys) in
        let symb_keys = Collections.VarSet.elements (snd keys) in
        let new_decls, f' =
          MapUnrollingSingle.unroll_declarations
            mty
            (const_keys, symb_keys)
            decls
        in
        new_decls, fun x -> f (f' x))
      (decls, fun x -> x)
      maplist
  in
  let final_decls, map_back2 =
    CleanupTuples.cleanup_declarations unrolled_decls
  in
  final_decls, map_back1 % map_back2
;;
