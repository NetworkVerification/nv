open Nv_datastructures.AdjGraph
open Nv_lang.Syntax
open SrpRemapping

(** Transform the solution based on the partitioned SRP's information. *)
val transform_solve : (exp, int) BatMap.t ref -> solve -> partitioned_srp -> partitioned_srp * solve

val transform_solve_inverted : solve -> partitioned_srp list -> (partitioned_srp * solve) list

(** Transform the assertion based on the partitioned SRP's information. *)
val transform_assert : exp -> partitioned_srp -> exp
