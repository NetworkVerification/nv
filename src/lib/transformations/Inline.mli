open Nv_lang.Syntax
open Nv_datastructures

val substitute : Var.t -> exp -> exp -> exp

val inline_exp : exp Env.t -> exp -> exp

val inline_declarations :
  declarations -> declarations
