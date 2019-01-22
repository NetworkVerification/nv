open Syntax

val substitute : Var.t -> exp -> exp -> exp

val inline_exp : exp Env.t -> exp -> exp

val inline_declarations :
  declarations -> declarations
