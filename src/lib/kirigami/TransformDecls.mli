open Nv_datastructures.AdjGraph
open Nv_lang.Syntax

(* Describe how the transfer function should be decomposed.
 * Some types of networks require different settings of this,
 * depending on how they transfer routes.
 * Future work will involve providing the transcomp as part of
 * a solution (when an interface is provided) to describe how
 * to decompose the transfer function.
 *  Figuring that out is future work. *)
type transcomp =
  (* Decompose the original transfer e into two parts e1 and e2,
   * where e1 is performed on the base~output edge and e2 is
   * performed on the input~base edge. *)
  | Decomposed of exp * exp
  (* Shorthand for (Decomposed e identity). *)
  | OutputTrans
  (* Shorthand for (Decomposed identity e). *)
  | InputTrans

val transform_solve
  :  transcomp:transcomp
  -> solve
  -> SrpRemapping.partitioned_srp
  -> solve * exp list * (exp, int) Batteries.Map.t

(* Wrap the given assert exp in a new exp that maps over new nodes.
 * TODO
 *)
val transform_assert : exp -> SrpRemapping.partitioned_srp -> exp
