open Nv_lang
open Nv_solution

val unroll_decls
  :  Console.info
  -> Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)
