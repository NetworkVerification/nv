open Nv_lang.Syntax
open Nv_solution

val unroll_declarations : declarations -> declarations * Solution.map_back
val unroll_net : network -> network * Solution.map_back
(* No SRP unrolling unless we store information about record types somehow *)
