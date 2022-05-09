(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax
open Nv_solution.Solution
open SrpRemapping

(** Add the predicates to the given partitions from the given interface. *)
val get_predicates : fragment list -> exp -> fragment list

(* Return a new set of declarations of all symbolics added by partitions. *)
val get_hyp_symbolics : ty -> fragment -> declarations

(** Given the partitioned SRP, transform the declarations. *)
val transform_declarations
  :  declarations
  -> fragment
  -> fragment * declarations
