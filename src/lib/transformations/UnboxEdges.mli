open Nv_lang.Syntax
open Nv_solution

(* Replace all edges with tuples of two nodes. Should be done after Map Unrolling
   (and any other transformations that rely on specifically having edge types). *)

val unbox_declarations : declarations -> declarations * Solution.map_back
val unbox_net : network -> network * Solution.map_back
val unbox_srp : srp_unfold -> srp_unfold * Solution.map_back
