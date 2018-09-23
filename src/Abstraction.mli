(** Given a graph and a destination node compute an abstraction function *)
val findAbstraction :
  Srp.srp -> Graph.Vertex.t -> AbstractionMap.abstractionMap

module FailuresAbstraction :
  sig  
    (** Given a concrete graph, an abstraction function, and a abstrId of an
        abstract node to split, tries to refine the abstraction leveraging
        the given path if possible *)
    val refineForFailures :
      Graph.t ->
      AbstractionMap.abstractionMap ->
      AbstractionMap.abstrId ->
      AbstractionMap.abstrId list -> AbstractionMap.abstractionMap
  end
     
(** [buildAbstractGraph g f] constructs the abstract graph from graph
   g and the abstraction f*)
val buildAbstractGraph : Graph.t -> AbstractionMap.abstractionMap -> Graph.t

(** [abstractToConcreteEdge g f ehat] returns the set of concrete
   edges that map to the abstract edge [ehat] *)
val abstractToConcreteEdge: Graph.t -> AbstractionMap.abstractionMap ->
                             Graph.Edge.t -> Graph.EdgeSet.t

(** [getEdgeMultiplicity g f ehat] returns the number of concrete
   edges that map to the abstract edge [ehat] *)  
val getEdgeMultiplicity: Graph.t -> AbstractionMap.abstractionMap ->
                         Graph.Edge.t -> int
