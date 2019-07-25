open Nv_core
open Nv_solution

val alpha_convert_exp : Nv_datatypes.Var.t Nv_datastructures.Env.t -> Syntax.exp -> Syntax.exp

val alpha_convert_declarations :
     Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)

val alpha_convert_net :
  Syntax.network
  -> Syntax.network * (Solution.t -> Solution.t)

val alpha_convert_srp :
  Syntax.srp_unfold -> Syntax.srp_unfold * (Solution.t -> Solution.t)
