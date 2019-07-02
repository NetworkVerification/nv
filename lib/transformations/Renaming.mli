open Syntax
open Solution

val alpha_convert_exp : Var.t Env.t -> exp -> exp

val alpha_convert_declarations :
     Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)

val alpha_convert_net :
  Syntax.network
  -> Syntax.network * (Solution.t -> Solution.t)

val alpha_convert_srp :
  Syntax.srp_unfold -> Syntax.srp_unfold * (Solution.t -> Solution.t)
