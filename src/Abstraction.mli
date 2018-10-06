(** [partialEvalTrans g trans] partially evaluates the transfer
   function for each edge on the graph g and returns a table from
   edges to expressions and their hash *)
val partialEvalTrans: Graph.t -> Syntax.exp -> (Graph.Edge.t, int * Syntax.exp) Hashtbl.t 

(** [partialEvalMerge g trans] partially evaluates the merge function
   for each vertex on the graph g and returns a table from vertices to
   expressions and their hash *)
val partialEvalMerge: Graph.t -> Syntax.exp -> (Graph.Vertex.t, int * Syntax.exp) Hashtbl.t
  
(** [findAbstraction g trans merge] computes an abstraction function
    for the network *)
val findAbstraction :
  Graph.t -> Syntax.exp -> Syntax.exp -> AbstractionMap.abstractionMap

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
