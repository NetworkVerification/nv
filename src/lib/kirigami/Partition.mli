(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang.Syntax

(** Convert a Syntax.network to a partitioned network.
 * This involves:
 * - changing the topology
 * - updating init, trans and merge for the new input/output nodes
 * - adding symbolic variables to represent hypotheses, with
 * require clauses providing assumptions on them
 * - updating or adding assert for the output nodes 
 *)
val open_network : network -> network

(** Create a new Syntax.declarations list from the given one,
 * where the partition and interface information is used to create a new network.
 * This involves:
 * - changing the topology
 * - updating init, trans and merge for the new input/output nodes
 * - adding symbolic variables to represent hypotheses, with
 * require clauses providing assumptions on them
 * - updating or adding assert for the output nodes 
 *)
(* val open_declarations : declarations -> declarations *)

(** Create a list of Syntax.declarations,
 * where a new set of declarations for a given network is produced
 * for each possible partition in the given declarations.
 *)
val divide_decls : declarations -> declarations list
