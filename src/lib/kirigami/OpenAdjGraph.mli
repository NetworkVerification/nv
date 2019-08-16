open Batteries
open Nv_datastructures
open AdjGraph

(* Internal AdjGraph.t structure *)
(* One Map for the input->base edges *)
(* One Map for the base->output edges *)
(* One Map for the broken base->base edges *)
type t = {
  graph: AdjGraph.t;
  inputs: Vertex.t VertexMap.t;
  outputs: Vertex.t VertexMap.t;
  broken: Vertex.t VertexMap.t;
}

(** add_new_input g v creates a new open graph with a new node u with an edge u~v *)
val add_new_input : t -> Vertex.t -> t
(** add_new_output g v creates a new open graph with a new node u with an edge v~u *)
val add_new_output : t -> Vertex.t -> t
(** partition_edge g e separates the edge e into an output-input pair *)
val partition_edge : t -> Edge.t -> t
(** to_node g v returns the base node that input node v has an edge to *)
val to_node : t -> Vertex.t -> Vertex.t
(** from_node g v returns the base node that output node v has an edge from *)
val from_node : t -> Vertex.t -> Vertex.t
(** input_nodes g returns an enumeration over the input nodes *)
val input_nodes : t -> Vertex.t Enum.t
(** output_nodes g returns an enumeration over the output nodes *)
val output_nodes : t -> Vertex.t Enum.t
