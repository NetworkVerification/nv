(** [partialEvalTrans g trans] partially evaluates the transfer
   function for each edge on the graph g and returns a table from
   edges to expressions and their hash *)
val partialEvalTrans: Graph.t -> Syntax.exp -> (Graph.Edge.t, int * Syntax.exp) Hashtbl.t 

(** [partialEvalMerge g trans] partially evaluates the merge function
   for each vertex on the graph g and returns a table from vertices to
   expressions and their hash *)
val partialEvalMerge: Graph.t -> Syntax.exp -> (Graph.Vertex.t, int * Syntax.exp) Hashtbl.t
  
(** [findAbstraction g trans merge ds] computes an abstraction function
    for the network *)
val findAbstraction :
  Graph.t -> (Graph.Edge.t, int * Syntax.exp) Hashtbl.t ->
  (Graph.Vertex.t, int * Syntax.exp) Hashtbl.t ->
  Graph.Vertex.t BatSet.t -> AbstractionMap.abstractionMap

module FailuresAbstraction :
  sig  
    (** Given a concrete graph, an abstraction function, and a abstrId of an
        abstract node to split, tries to refine the abstraction leveraging
        the given path if possible *)
    val refineForFailures :
      Graph.t ->
      AbstractionMap.abstractionMap ->
      (Graph.Edge.t, Var.t) BatMap.t ->
      Solution.t ->
      AbstractionMap.abstractionMap
  end

     
module BuildAbstractNetwork :
sig
  (** [buildAbstractNetwork f g mergeMap transMap initMap assertMap dst attrTy k] builds the
   declarations of the abstract network *)
  val buildAbstractNetwork : AbstractionMap.abstractionMap -> Graph.t ->
                             (Graph.Vertex.t, int * Syntax.exp) Hashtbl.t ->
                             (Graph.Edge.t, int * Syntax.exp) Hashtbl.t ->
                             (Graph.Vertex.t, Syntax.exp) Hashtbl.t ->
                             (Graph.Vertex.t, Syntax.exp) Hashtbl.t ->
                             Graph.Vertex.t BatSet.t ->
                             Syntax.ty ->
                             (Syntax.var * Syntax.ty_or_exp) list ->
                             int -> ((Graph.Edge.t, Var.t) BatMap.t) * Syntax.declarations

  (** [abstractToConcreteEdge g f ehat] returns the set of concrete
   edges that map to the abstract edge [ehat] *)
  val abstractToConcreteEdge: Graph.t -> AbstractionMap.abstractionMap ->
                              Graph.Edge.t -> Graph.EdgeSet.t

  (** [getEdgeMultiplicity g f ehat] returns the number of concrete
   edges that map to the abstract edge [ehat] *)  
  val getEdgeMultiplicity: Graph.t -> AbstractionMap.abstractionMap ->
                           Graph.Edge.t -> int
end
