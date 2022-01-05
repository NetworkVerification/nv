open Nv_lang.Syntax

(* hardcoded record labels *)
val bgplabels : String.t list
val riblabels : String.t list

(* a rib attribute with all fields set to None *)
val defaultRib : exp

val node_to_int : var
val edge_to_int_pair : var

(* Declaration for a function to match nodes with integers.
 * Necessary for dealing with partitioning nodes. *)
val node_to_int_decl : int -> declaration

(* Declaration for a function to match edges with integer pairs.
 *)
val edge_to_int_pair_decl : (node * node) list -> declaration

(* `mapi_record f ls e` returns a new ERecord exp with the given
 * labels `ls` updated according to `f` called on `l` in `ls` and `eproject e l`. *)
val mapi_record : (String.t * exp -> exp) -> string list -> exp -> exp

(* Shorthand for `mapi_record` called with a particular label to update *)
val update_record_at : (exp -> exp) -> string -> string list -> exp -> exp
val update_comms : (exp * exp) list -> exp
val assert_bgp : exp -> (exp -> exp) -> exp

val descend
  :  (var list -> exp -> exp)
  -> (var list -> exp -> bool)
  -> var list
  -> exp
  -> exp
