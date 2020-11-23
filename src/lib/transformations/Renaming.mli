open Nv_lang
open Nv_solution

val alpha_convert_exp
  :  Nv_datastructures.Var.t Nv_datastructures.Env.t
  -> Syntax.exp
  -> Syntax.exp

val alpha_convert_declarations
  :  Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)

val alpha_convert_declarations_or_group
  :  Syntax.declarations_or_group
  -> Syntax.declarations_or_group * (Solution.t -> Solution.t)
