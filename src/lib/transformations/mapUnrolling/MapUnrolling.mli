open Nv_lang
open Nv_solution

val unroll_decls
  :  Console.info
  -> Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)

val unroll
  :  Console.info
  -> Syntax.declarations_or_group
  -> Syntax.declarations_or_group * (Solution.t -> Solution.t)
