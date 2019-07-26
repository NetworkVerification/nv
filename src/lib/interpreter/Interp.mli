open Nv_lang.Syntax

val interp_exp : env -> exp -> value

val interp_op : env -> ty -> op -> exp list -> value

val interp : exp -> value

val interp_closure : closure -> value list -> value

val apply : env -> func -> value -> value
