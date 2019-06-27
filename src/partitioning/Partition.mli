(* Partitioning utilities and partition interface definitions *)
open Batteries

type t

(* Return true if an edge is cross-partition, given a partition function *)
val is_cross_partition : (AdjGraph.Edge.t -> int) -> AdjGraph.Edge.t -> bool

(* The interface module used for partitioning and composing interfaces *)
module Interface :
  sig
    type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * t
  end

module InterfaceSet : Set.S with type elt = Interface

(* module Interface : Set.S with type elt = (AdjGraph.Vertex.t * AdjGraph.Vertex.t * t) *)

(* Default values for interface: *)
(* When partitioning an SRP into open SRPs, we want to be able to reason about
 * the values "entering" at the input nodes and "leaving" at the output nodes.
 * While open SRPs are encoded the same as closed SRPs, with the exception of
 * the additional functions `in` and `out` to associate inputs and outputs with
 * base nodes, when partitioning an SRP to **infer** its solutions, it is
 * useful to have a default starting value to work from.
 *)

(* Possible hypotheses used when annotating interface edges *)
type hypothesis =
  | None (* edge is not cross-partition *)
  | Infer (* infer the input's hypothesis, starting from a default *)
  | Annotate of t (* use the given attribute as the input's hypothesis *)

(* get the input node's attribute for the specified hypothesis *)
val hyp_to_opt_att : hypothesis -> t option
