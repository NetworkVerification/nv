open Syntax
open Memoization

val empty_env : env

val apply : env -> func -> value -> value

val update_value : env -> Var.t -> value -> env

val interp_exp : env -> exp -> value

val interp_op : env -> ty -> op -> exp list -> value

val interp : exp -> value

val interp_closure : closure -> value list -> value

val interp_partial : MemoizeExp.t -> MemoizeExp.t
val interp_partial_opt : MemoizeExp.t -> MemoizeExp.t


val interp_partial_fun : MemoizeExp.t -> value list -> MemoizeExp.t

module Full :
sig
  val interp_partial : exp -> exp
  val interp_partial_fun: exp -> exp list -> exp
end
