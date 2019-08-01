open Nv_lang.Syntax

val substitute : Nv_datastructures.Var.t -> exp -> exp -> exp

val inline_exp : exp Nv_datastructures.Env.t -> exp -> exp

val inline_declarations :
  declarations -> declarations
