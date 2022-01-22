open Nv_datastructures.AdjGraph
open Nv_lang.Syntax
open SrpRemapping

(** Add the predicates to the given partitions from the given interface. *)
val get_predicates : partitioned_srp list -> exp -> partitioned_srp list

(** Transform the assertion based on the partitioned SRP's information. *)
val transform_assert : exp -> partitioned_srp -> exp
