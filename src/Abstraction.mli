(** [partialEvalTrans g trans] partially evaluates the transfer
   function for each edge on the graph g and returns a table from
   edges to expressions and their hash *)
val partialEvalTrans: AdjGraph.t -> Syntax.exp -> (AdjGraph.Edge.t, int * Syntax.exp) Hashtbl.t 

(** [partialEvalMerge g trans] partially evaluates the merge function
   for each vertex on the graph g and returns a table from vertices to
   expressions and their hash *)
val partialEvalMerge: AdjGraph.t -> Syntax.exp -> (AdjGraph.Vertex.t, int * Syntax.exp) Hashtbl.t
  
(** [findAbstraction g trans merge ds] computes an abstraction function
    for the network *)
val findAbstraction :
  AdjGraph.t -> (AdjGraph.Edge.t, int * Syntax.exp) Hashtbl.t ->
  (AdjGraph.Vertex.t, int * Syntax.exp) Hashtbl.t ->
  AdjGraph.VertexSet.t -> AbstractionMap.abstractionMap

module FailuresAbstraction :
  sig  
    (** [refineForFailures draw file g finit f failVars sol k dst attr]
       decides whether there is need to further refine the
       abstraction. *)
    val refineForFailures :
      bool ->
      string ->
      AdjGraph.t ->
      AbstractionMap.abstractionMap ->
      AbstractionMap.abstractionMap ->
      Var.t AdjGraph.EdgeMap.t ->
      Solution.t ->
      int ->
      AdjGraph.VertexSet.t ->
      Syntax.ty ->
      AbstractionMap.abstractionMap option

    val refineK : AdjGraph.t -> AbstractionMap.abstractionMap ->
                  AdjGraph.VertexSet.t -> int -> AbstractionMap.abstractionMap
  end

     
module BuildAbstractNetwork :
sig
  (** [buildAbstractNetwork f g mergeMap transMap initMap assertMap dst attrTy k] builds the
   declarations of the abstract network *)
  val buildAbstractNetwork : AbstractionMap.abstractionMap -> AdjGraph.t ->
                             (AdjGraph.Vertex.t, int * Syntax.exp) Hashtbl.t ->
                             (AdjGraph.Edge.t, int * Syntax.exp) Hashtbl.t ->
                             (AdjGraph.Vertex.t, Syntax.exp) Hashtbl.t ->
                             (AdjGraph.Vertex.t, Syntax.exp) Hashtbl.t ->
                             AdjGraph.VertexSet.t ->
                             Syntax.ty ->
                             Slicing.Prefix.t ->
                             (Syntax.var * Syntax.ty_or_exp) list ->
                             int -> (Var.t AdjGraph.EdgeMap.t) * Syntax.declarations

  (** [abstractToConcreteEdge g f ehat] returns the set of concrete
   edges that map to the abstract edge [ehat] *)
  val abstractToConcreteEdge: AdjGraph.t -> AbstractionMap.abstractionMap ->
                              AdjGraph.Edge.t -> AdjGraph.EdgeSet.t

  (** [getEdgeMultiplicity g f ehat] returns the number of concrete
   edges that map to the abstract edge [ehat] *)  
  val getEdgeMultiplicity: AdjGraph.t -> AbstractionMap.abstractionMap ->
                           AdjGraph.Edge.t -> int
end
