open Batteries
open Nv_datastructures
open AdjGraph

type vertex_vertex_map = Vertex.t VertexMap.t
(* Internal AdjGraph.t structure *)
(* One Map for the input->base edges *)
(* One Map for the base->output edges *)
(* One Map for the associated output->input edges *)
type t = {
  graph: AdjGraph.t;
  inputs: vertex_vertex_map;
  outputs: vertex_vertex_map;
  broken: vertex_vertex_map;
}

(** from_graph g creates a new open graph from a (closed) graph *)
val from_graph : AdjGraph.t -> t
(** partition_edge g e separates the edge e into an output-input pair *)
val partition_edge : t -> Edge.t -> t
(** partition_graph g edges separates each edge in the given set *)
val partition_graph : t -> EdgeSet.t -> t
(** to_node g v returns the base node that input node v has an edge to *)
val to_node : t -> Vertex.t -> Vertex.t
(** from_node g v returns the base node that output node v has an edge from *)
val from_node : t -> Vertex.t -> Vertex.t
(** broken_edge g v returns the base edge that output node v forms the replacement of *)
val broken_edge : t -> Vertex.t -> Edge.t
(** input_nodes g returns an enumeration over the input nodes *)
val input_nodes : t -> Vertex.t Enum.t
(** output_nodes g returns an enumeration over the output nodes *)
val output_nodes : t -> Vertex.t Enum.t
(** compose_edge g out in removes the output and input node pair and composes the edge they refer to *)
val compose_edge : t -> Vertex.t -> Vertex.t -> t
