open Nv_lang
open Nv_solution

val rename_declarations
  :  Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)
