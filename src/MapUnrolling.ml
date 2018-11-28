(* Unroll all map types contained in decls. Cannot handle polymorphism,
   so requires that inlining has been run first.

   Returns an equivalent set of decls where all map types have been
   replaced with tuple types, and a function which converts a Solution
   to the new decls into a solution for the old decls. *)
let unroll info decls =
  let maplist =
    MapUnrollingUtils.collect_map_types_and_keys decls
  in
  let final_decls, map_back =
    List.fold_left
      (fun (decls, f) (mty, keys) ->
         let keys = (Collections.ExpSet.elements keys) in
         let new_decls =
           MapUnrolling2.unroll_one_map_type mty keys decls
         in
         let f' =
           MapUnrollingConversion.convert_solution mty keys decls
         in
         (Typing.infer_declarations info new_decls,
          (fun x -> f (f' x))
         )
      )
      (decls, (fun x -> x))
      maplist
  in
  final_decls, [], map_back
;;

exception Cannot_unroll of Syntax.exp
