open Nv_core.Syntax

val substitute : Nv_datatypes.Var.t -> exp -> exp -> exp

val inline_exp : exp Nv_datastructures.Env.t -> exp -> exp

val inline_declarations :
  declarations -> declarations
