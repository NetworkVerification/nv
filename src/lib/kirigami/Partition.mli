(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax
open Nv_solution.Solution

val of_decls : declaration list -> declarations_or_group

(** Given the partitioned SRP, transform the declarations. *)
val transform_declarations
  :  declarations
  -> SrpRemapping.partitioned_srp
  -> declaration_groups
