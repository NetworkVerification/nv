(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures

(* Return true if an edge is cross-partition, given a partition function *)
val is_cross_partition : (AdjGraph.Vertex.t -> int) -> AdjGraph.Edge.t -> bool

(* The interface module used for partitioning and composing interfaces *)
module Interface(S: Interfaces.OrderedType) :
  sig
    type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * S.t option

    val create : AdjGraph.Edge.t -> S.t option -> t

    val compare : t -> t -> int
end

module InterfaceSet(S: Interfaces.OrderedType) : Set.S with type elt = Interface(S).t

(* module Interface : Set.S with type elt = (AdjGraph.Vertex.t * AdjGraph.Vertex.t * t) *)

(* Default values for interface: *)
(* When partitioning an SRP into open SRPs, we want to be able to reason about
 * the values "entering" at the input nodes and "leaving" at the output nodes.
 * While open SRPs are encoded the same as closed SRPs, with the exception of
 * the additional functions `in` and `out` to associate inputs and outputs with
 * base nodes, when partitioning an SRP to **infer** its solutions, it is
 * useful to have a default starting value to work from.
 *)

(* Graph transformations *)
(* val partition_graph : OpenAdjGraph.t -> InterfaceSet.t -> OpenAdjGraph.t *)
