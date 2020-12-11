open Nv_datastructures.AdjGraph
open Nv_lang.Syntax

val transform_solve
  :  solve
  -> SrpRemapping.partitioned_srp
  -> solve

val transform_assert : exp -> SrpRemapping.partitioned_srp -> exp
