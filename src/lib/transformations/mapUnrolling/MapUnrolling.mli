open Nv_lang
open Nv_solution

val unroll
  :  Console.info
  -> Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)

val unroll_with_maplist
  :  Console.info
  -> maplist:MapUnrollingUtils.maplist
  -> Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)
