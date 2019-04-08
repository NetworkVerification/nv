open Syntax

val unroll :
  declarations -> 
  declarations * (Solution.t -> Solution.t)
