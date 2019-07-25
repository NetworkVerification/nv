open Syntax
open Memoization

val interp_partial : MemoizeExp.t -> MemoizeExp.t
val interp_partial_opt : MemoizeExp.t -> MemoizeExp.t


val interp_partial_fun : MemoizeExp.t -> value list -> MemoizeExp.t
