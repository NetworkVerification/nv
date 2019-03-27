open Syntax

val unroll :
     Console.info
  -> declarations
  -> declarations  * (Solution.t -> Solution.t)

