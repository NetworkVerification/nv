open Nv_datastructures.AdjGraph
open Nv_lang.Syntax
open SrpRemapping

(** Return a new partitioned SRP, with updated predicate information from the given interface. *)
val update_preds : exp -> partitioned_srp -> partitioned_srp

(** Transform the solution based on the partitioned SRP's information. *)
val transform_solve : solve -> partitioned_srp -> partitioned_srp * solve

(** Transform the assertion based on the partitioned SRP's information. *)
val transform_assert : exp -> partitioned_srp -> exp
