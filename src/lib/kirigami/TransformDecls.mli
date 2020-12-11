open Nv_datastructures.AdjGraph
open Nv_lang.Syntax

val transform_solve
  :  solve
  -> SrpRemapping.partitioned_srp
  -> solve * exp list * (var * ty_or_exp) list * (exp, int) Batteries.Map.t

val transform_assert : exp -> SrpRemapping.partitioned_srp -> exp
