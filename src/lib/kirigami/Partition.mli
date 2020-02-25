(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang.Syntax

(** Create a list of Syntax.declarations,
 * where a new set of declarations for a given network is produced
 * for each possible partition in the given declarations.
*)
val divide_decls : declarations -> declarations list
