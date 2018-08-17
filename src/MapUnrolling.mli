open Syntax

exception Cannot_unroll of exp

val unroll :
     Console.info
  -> declarations
  -> declarations * (Var.t * exp) list * (Solution.t -> Solution.t)
