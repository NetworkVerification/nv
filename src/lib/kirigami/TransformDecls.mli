open Nv_datastructures.AdjGraph
open Nv_lang.Syntax
open SrpRemapping

(** Update the list of variables for the partitioned SRP from the given list of symbolics. *)
val update_vars_from_symbolics : partitioned_srp -> (var * ty_or_exp) list -> partitioned_srp

(** Transform the solution based on the partitioned SRP's information. *)
val transform_solve : solve -> partitioned_srp -> partitioned_srp * solve

(** Transform the assertion based on the partitioned SRP's information. *)
val transform_assert : exp -> partitioned_srp -> exp
