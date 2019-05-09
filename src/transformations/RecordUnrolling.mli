open Syntax

val unroll :
  declarations -> 
  declarations * (Solution.t -> Solution.t)


val unroll_net :
  network -> 
  network * (Solution.t -> Solution.t)
