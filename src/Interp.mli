open Syntax

val empty_env : env

val apply : env -> func -> value -> value

val update_value : env -> Var.t -> value -> env

val interp_exp : env -> exp -> value

val interp_op : env -> ty -> op -> exp list -> value

val interp : exp -> value

val interp_closure : closure -> value list -> value

val interp_partial : Syntax.MemoizeExp.t -> Syntax.MemoizeExp.t
val interp_partial_opt : Syntax.MemoizeExp.t -> Syntax.MemoizeExp.t
    

val interp_partial_fun : Syntax.MemoizeExp.t -> value list -> Syntax.MemoizeExp.t

module Full :
sig
  val interp_partial : exp -> exp
  val interp_partial_fun: exp -> exp list -> exp
end
