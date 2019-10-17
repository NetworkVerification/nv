(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang.Syntax

(* Return true if an edge is cross-partition, given a partition function *)
val is_cross_partition : (AdjGraph.Vertex.t -> int) -> AdjGraph.Edge.t -> bool

(* Default values for interface: *)
(* When partitioning an SRP into open SRPs, we want to be able to reason about
 * the values "entering" at the input nodes and "leaving" at the output nodes.
 * While open SRPs are encoded the same as closed SRPs, with the exception of
 * the additional functions `in` and `out` to associate inputs and outputs with
 * base nodes, when partitioning an SRP to **infer** its solutions, it is
 * useful to have a default starting value to work from.
 *)

(* Graph transformations *)
(* conversion of Syntax.network to opened network *)
type onetwork =
  {
    attr_type       : ty;
    init            : exp;
    trans           : exp;
    merge           : exp;
    assertion       : exp option;
    symbolics       : (var * ty_or_exp) list;
    defs            : (var * ty option * exp) list;
    utys            : (var * ty) list;
    requires        : exp list;
    ograph          : OpenAdjGraph.t
  }

(** Convert a Syntax.network to an onetwork *)
val open_network : network -> onetwork
(* Create a partition interface from a Syntax.network *)
val partition_interface: exp option -> exp option -> AdjGraph.t -> value option AdjGraph.EdgeMap.t
