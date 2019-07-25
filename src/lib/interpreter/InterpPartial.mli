open Memoization

val interp_partial : MemoizeExp.t -> MemoizeExp.t
val interp_partial_opt : MemoizeExp.t -> MemoizeExp.t


val interp_partial_fun : MemoizeExp.t -> Nv_core.Syntax.value list -> MemoizeExp.t
