open Nv_lang.Syntax

(* hardcoded record labels *)
val bgplabels : String.t list
val riblabels : String.t list

(* `mapi_record f ls e` returns a new ERecord exp with the given
 * labels `ls` updated according to `f` called on `l` in `ls` and `eproject e l`. *)
val mapi_record : (String.t * exp -> exp) -> string list -> exp -> exp

(* Shorthand for `mapi_record` called with a particular label to update *)
val update_record_at : (exp -> exp) -> string -> string list -> exp -> exp
val update_comms : (exp * exp) list -> exp

val descend
  :  ('a -> exp -> exp)
  -> ('a -> exp -> bool)
  -> (exp -> 'a -> 'a)
  -> 'a
  -> exp
  -> exp
