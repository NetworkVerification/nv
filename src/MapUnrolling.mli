open Syntax

val unroll :
     Console.info
  -> declarations
  -> declarations * (Var.t * exp) list * (Solution.t -> Solution.t)
