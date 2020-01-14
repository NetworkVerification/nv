open Batteries
open Nv_datastructures
open AdjGraph

type vertex_vertex_map = Vertex.t VertexMap.t
(* Internal AdjGraph.t structure *)
(* One Map for the input->base edges *)
(* One Map for the base->output edges *)
(* One Map for the associated output->input edges *)
type interfaces = {
  inputs: vertex_vertex_map;
  outputs: vertex_vertex_map;
  broken: vertex_vertex_map;
}

val intf_empty : interfaces

type t = AdjGraph.t * interfaces

(** partition_edge g e separates the edge e into an output-input pair *)
val partition_edge : AdjGraph.t -> interfaces -> Edge.t -> t
(** partition_graph g edges separates each edge in the given set *)
val partition_graph : AdjGraph.t -> interfaces -> EdgeSet.t -> t
(** to_node g v returns the base node that input node v has an edge to *)
val to_node : interfaces -> Vertex.t -> Vertex.t
(** from_node g v returns the base node that output node v has an edge from *)
val from_node : interfaces -> Vertex.t -> Vertex.t
(** broken_edge g v returns the base edge that output node v forms the replacement of *)
val broken_edge : interfaces -> Vertex.t -> Edge.t
(** input_nodes g returns an enumeration over the input nodes *)
val input_nodes : interfaces -> Vertex.t Enum.t
(** output_nodes g returns an enumeration over the output nodes *)
val output_nodes : interfaces -> Vertex.t Enum.t
(** compose_edge g out in removes the output and input node pair and composes the edge they refer to *)
val compose_edge : AdjGraph.t -> interfaces -> Vertex.t -> Vertex.t -> t

val map_vertices_to_parts : Vertex.t list -> (Vertex.t -> int) -> (int VertexMap.t * int)
val divide_vertices : int VertexMap.t -> int -> Vertex.t list list
val divide_edges : Edge.t list -> (Vertex.t list list) -> (Edge.t list list)
