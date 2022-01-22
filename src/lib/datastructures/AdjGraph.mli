open Nv_utils.PrimitiveCollections

module Vertex : sig
  type t = int (* Really should be Syntax.node, but that causes a dependency loop *)

  val to_string : t -> string
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int
end

(* graph *)
include module type of Graph.Persistent.Digraph.Concrete (Vertex)

module Edge : sig
  include module type of E

  val to_string : t -> string
end

module VertexMap : BetterMap.S with type key = Vertex.t
module VertexSet : BetterSet.S with type elt = Vertex.t
module VertexSetSet : BetterSet.S with type elt = VertexSet.t
module VertexSetMap : BetterMap.S with type key = VertexSet.t
module EdgeSet : BetterSet.S with type elt = Edge.t
module EdgeMap : BetterMap.S with type key = Edge.t

(** Graph creation **)
val create : int -> t (* Disconnected graph with n nodes *)

val of_edges : Edge.t list -> t (* Graph with all edges & nodes in the list *)

(** Vertex/Edge retrieval **)
val vertices : t -> Vertex.t list

val edges : t -> Edge.t list

(** Printing *)
val to_string : t -> string

(** computes min-cut between s and t and the returns the min-cut and the S and T sets *)
val min_cut : t -> Vertex.t -> Vertex.t -> EdgeSet.t * VertexSet.t * VertexSet.t

module DrawableGraph : sig
  val graph_dot_file : int -> string -> string

  (* [drawGraph g name] draws the graph g in a file called name.jpg *)
  val drawGraph : t -> string -> unit
end
