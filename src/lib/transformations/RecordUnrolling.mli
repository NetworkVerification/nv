open Nv_solution

val unroll :
  Nv_core.Syntax.declarations -> 
  Nv_core.Syntax.declarations * (Solution.t -> Solution.t)


val unroll_net :
  Nv_core.Syntax.network -> 
  Nv_core.Syntax.network * (Solution.t -> Solution.t)
