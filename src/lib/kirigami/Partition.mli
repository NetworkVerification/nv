(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax
open Nv_solution.Solution
open SrpRemapping

(* Return a new set of declarations of all symbolics added by partitions. *)
val get_hyp_symbolics : ty -> partitioned_srp -> declarations

(** Given the partitioned SRP, transform the declarations. *)
val transform_declarations
  :  declarations
  -> partitioned_srp
  -> partitioned_srp * declarations
