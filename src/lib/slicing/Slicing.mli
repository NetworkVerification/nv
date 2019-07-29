open Nv_datastructures

(** The type of network prefixes *)
module Prefix : Map.OrderedType with type t = Integer.t * Integer.t

module PrefixSet : BatSet.S with type elt = Prefix.t

module PrefixMap : BatMap.S with type key = Prefix.t

module PrefixSetSet : BatSet.S with type elt = PrefixSet.t

(** The type of network slices *)
type network_slice =
  { net          : Nv_lang.Syntax.network;
    prefixes     : PrefixSet.t;
    destinations : AdjGraph.VertexSet.t
  }

val printPrefix : Prefix.t -> string

val printPrefixes : PrefixSet.t -> string

(** [relevantPrefixes assertTable] returns the prefixes that are used by the
   assertion function*)
val relevantPrefixes: (AdjGraph.Vertex.t, Nv_lang.Syntax.exp) Hashtbl.t -> PrefixSet.t

(** [partialEvalOverNodes n e] returns a table that maps each node to
   its respective expression *)
val partialEvalOverNodes: AdjGraph.Vertex.t -> Nv_lang.Syntax.exp -> (AdjGraph.Vertex.t, Nv_lang.Syntax.exp) Hashtbl.t

(** [partialEvalOverNodes edges e] returns a table that maps each edge to
   its respective expression *)
val partialEvalOverEdges: AdjGraph.Edge.t list -> Nv_lang.Syntax.exp ->
                          (AdjGraph.Edge.t, Nv_lang.Syntax.exp) Hashtbl.t

(** [findInitialSlices n] returns a map from prefix to set of nodes,
   with the property that each node in the set announces this
   prefix. *)
val findInitialSlices: (AdjGraph.Vertex.t, Nv_lang.Syntax.exp) Hashtbl.t ->
                       (AdjGraph.VertexSet.t) PrefixMap.t

val findRelevantNodes: (AdjGraph.Vertex.t, Nv_lang.Syntax.exp) Hashtbl.t -> AdjGraph.VertexSet.t

val groupPrefixesByVertices: AdjGraph.VertexSet.t PrefixMap.t -> PrefixSetSet.t

val createNetwork: Nv_lang.Syntax.declarations -> Nv_lang.Syntax.network

val createSlices: Nv_lang.Console.info -> Nv_lang.Syntax.network -> network_slice list
