open Nv_lang
open Nv_solution

val rename_declarations :
     Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)

val rename_net :
  Syntax.network
  -> Syntax.network * (Solution.t -> Solution.t)

val rename_srp :
  Syntax.srp_unfold -> Syntax.srp_unfold * (Solution.t -> Solution.t)
