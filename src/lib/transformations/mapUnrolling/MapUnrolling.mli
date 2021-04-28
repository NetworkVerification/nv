open Nv_lang
open Nv_solution

val unroll
  :  Console.info
  -> Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)
