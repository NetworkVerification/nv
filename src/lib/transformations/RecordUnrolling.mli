open Nv_solution

val unroll :
  Nv_lang.Syntax.declarations -> 
  Nv_lang.Syntax.declarations * (Solution.t -> Solution.t)


val unroll_net :
  Nv_lang.Syntax.network -> 
  Nv_lang.Syntax.network * (Solution.t -> Solution.t)
