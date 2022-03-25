open Nv_lang.Collections

(**
   Each entry in this list is:
   * A map type
   * The set of constant keys that are used for the map
   * The set of symbolic variable keys that are used for the map

   Note the nested tuple type.
*)
type maplist = (Nv_lang.Syntax.ty * (ExpSet.t * VarSet.t)) list

val maplist_to_string : maplist -> string

(** Given a program on which type inference has been run, goes through
   it and returns a list of each map type which appears in that program,
   combined with the set of keys used for that map type.
*)
val collect_map_types_and_keys : Nv_lang.Syntax.declarations -> maplist
