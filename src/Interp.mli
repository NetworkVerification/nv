open Syntax

val empty_env : env

val apply : env -> func -> value -> value

val update_value : env -> Var.t -> value -> env

val interp_exp : env -> exp -> value

val interp_op : env -> ty -> op -> exp list -> value

val interp : exp -> value

val interp_closure : closure -> value list -> value
