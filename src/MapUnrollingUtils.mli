(* Each entry in this list is a pair of a map type, as well as
   the set of keys which appear in any MGet expression for that
   map type. *)
type maplist = (Syntax.ty * Syntax.exp list) list

val maplist_to_string : maplist -> string

(* Given a program on which type inference has been run, goes through
   it and returns a list of each map type which appears in that program,
   combined with the set of keys used for that map type.
*)
val collect_map_types_and_keys : Syntax.declarations -> maplist
