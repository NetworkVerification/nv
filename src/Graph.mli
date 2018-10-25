open Unsigned

module Vertex :
  sig
    type t = Unsigned.UInt32.t

    val printVertex : t -> string
    val compare : t -> t -> int
  end

module Edge : Map.OrderedType with type t = UInt32.t * UInt32.t

module VertexMap : Map.S with type key = Vertex.t

module VertexSet : Set.S with type elt = Vertex.t

module EdgeSet : Set.S with type elt = Edge.t

(* VertexMap auxiliaries *)

val vertex_map_to_string : ('a -> string) -> 'a VertexMap.t -> string

val print_vertex_map : ('a -> string) -> 'a VertexMap.t -> unit

(* graph *)

type t
  
(* raise BadVertex if a vertex v does not belong to a graph's set of vertices, ie: 0..num_vertex-1 *)

exception BadVertex of UInt32.t

val good_vertex : t -> Vertex.t -> unit

val good_graph : t -> unit

(* create a graph with i vertices named 0..i-1 *)

val create : UInt32.t -> t

(* number of vertices in the graph (named 0..i-1) *)

val num_vertices : t -> UInt32.t

  
val fold_vertices : (Vertex.t -> 'a -> 'a) -> UInt32.t -> 'a -> 'a
  
(** Vertices in the adjacency graph *)
val get_vertices : t -> Vertex.t BatSet.t
  
(* edges in the graph *)

val edges : t -> (UInt32.t * UInt32.t) list

(* add_edge g e adds directed edge e to g *)

val add_edge : t -> Edge.t -> t

(* add_edge g l adds all directed edges in l to g *)

val add_edges : t -> Edge.t list -> t

(* add_edge g e adds directed edge e to g *)

val remove_edge : t -> Edge.t -> t

(* neighbors g v returns neighbors of v in g; raise BadVertex if v invalid *)

val neighbors : t -> Vertex.t -> Vertex.t list

(* print graph *)

val print : t -> unit

(* graph to string *)

val to_string : t -> string
