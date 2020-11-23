open Nv_lang
open Nv_solution

val rename_declarations_or_group
  :  Syntax.declarations_or_group
  -> Syntax.declarations_or_group * (Solution.t -> Solution.t)
