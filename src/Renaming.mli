open Syntax
open Solution

val alpha_convert_exp : Var.t Env.t -> exp -> exp

val alpha_convert_declarations :
  Syntax.declarations -> Syntax.declarations * (Solution.t -> Solution.t)
