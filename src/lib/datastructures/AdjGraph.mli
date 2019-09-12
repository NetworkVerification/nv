module Vertex :
  sig
    type t = int (* Really should be Syntax.node, but that causes a dependency loop *)

    val to_string : t -> string
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
  end

(* graph *)
include module type of Graph.Persistent.Graph.Concrete (Vertex)

module Edge :
  sig
    include module type of E
    val to_string : t -> string
  end

module VertexMap : BatMap.S with type key = Vertex.t

module VertexSet : BatSet.S with type elt = Vertex.t
module VertexSetSet : BatSet.S with type elt = VertexSet.t
module VertexSetMap : BatMap.S with type key = VertexSet.t

module EdgeSet : BatSet.S with type elt = Edge.t

module EdgeMap : BatMap.S with type key = Edge.t

(* VertexMap auxiliaries *)

val vertex_map_to_string : ('a -> string) -> 'a VertexMap.t -> string

val print_vertex_map : ('a -> string) -> 'a VertexMap.t -> unit

(* raise BadVertex if a vertex v does not belong to a graph's set of vertices, ie: 0..num_vertex-1 *)
exception BadVertex of Vertex.t

val good_vertex : t -> Vertex.t -> unit

val good_graph : t -> unit

(* create a graph with i vertices named 0..i-1 *)
val create : int -> t

(** Create an incrementing set of vertices given an integer *)
val create_vertices : int -> VertexSet.t

(** fold over a set of vertices from 0 to i-1 *)
val fold_vertices : (Vertex.t -> 'a -> 'a) -> Vertex.t -> 'a -> 'a

(** Vertices in the adjacency graph *)
val get_vertices : t -> VertexSet.t

(** edges in the graph *)
val edges : t -> (Vertex.t * Vertex.t) list

(** of_edges l creates a new graph with all nodes and edges given in l *)
val of_edges : (Vertex.t * Vertex.t) list -> t

(** add_edges g l adds all directed edges in l to g *)
val add_edges : t -> Edge.t list -> t

(** neighbors g v returns neighbors of v in g; raise BadVertex if v invalid *)
val neighbors : t -> Vertex.t -> Vertex.t list

(** print graph *)
val print : t -> unit

(** graph to string *)
val to_string : t -> string

(** computes min-cut between s and t and the returns the min-cut and the S and T sets *)
val min_cut : t -> Vertex.t -> Vertex.t -> EdgeSet.t * VertexSet.t * VertexSet.t

module DrawableGraph :
sig

  val graph_dot_file: int -> string -> string
  (** [drawGraph g name] draws the graph g in a file called name.jpg *)
  val drawGraph : t -> string -> unit
end
