open Batteries
open Nv_datastructures

(* Internal AdjGraph.t structure *)
(* One AuxEdges set for the input->base edges *)
(* One AuxEdges set for the base->output edges *)
type t

(** Set tracking auxiliary edges *)
module AuxEdges : Set.S with type elt = AdjGraph.Edge.t

(** add_new_in g v creates a new open graph with a new node u with an edge u~v *)
val add_new_in : t -> AdjGraph.Vertex.t -> t

(** add_new_out g v creates a new open graph with a new node u with an edge v~u *)
val add_new_out : t -> AdjGraph.Vertex.t -> t

val partition_edge : t -> AdjGraph.Edge.t -> t

(** to_node g v returns the base node that input node v has an edge to *)
val to_node : t -> AdjGraph.Vertex.t -> AdjGraph.Vertex.t

(** from_node g v returns the base node that output node v has an edge from *)
val from_node : t -> AdjGraph.Vertex.t -> AdjGraph.Vertex.t
