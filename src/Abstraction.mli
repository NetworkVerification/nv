(** Sets of abstract nodes *)
module AbstractNodeSet :
  sig
    type t
    val empty : t
    val is_empty : t -> bool
    val mem : AbstractionMap.AbstractNode.t -> t -> bool
    val add : AbstractionMap.AbstractNode.t -> t -> t
    val singleton : AbstractionMap.AbstractNode.t -> t
    val remove : AbstractionMap.AbstractNode.t -> t -> t
    val union : t -> t -> t
    val inter : t -> t -> t
    val diff : t -> t -> t
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val subset : t -> t -> bool
    val iter : (AbstractionMap.AbstractNode.t -> unit) -> t -> unit
    val map :
      (AbstractionMap.AbstractNode.t -> AbstractionMap.AbstractNode.t) ->
      t -> t
    val fold : (AbstractionMap.AbstractNode.t -> 'a -> 'a) -> t -> 'a -> 'a
    val for_all : (AbstractionMap.AbstractNode.t -> bool) -> t -> bool
    val exists : (AbstractionMap.AbstractNode.t -> bool) -> t -> bool
    val filter : (AbstractionMap.AbstractNode.t -> bool) -> t -> t
    val partition : (AbstractionMap.AbstractNode.t -> bool) -> t -> t * t
    val cardinal : t -> int
    val elements : t -> AbstractionMap.AbstractNode.t list
    val min_elt : t -> AbstractionMap.AbstractNode.t
    val min_elt_opt : t -> AbstractionMap.AbstractNode.t option
    val max_elt : t -> AbstractionMap.AbstractNode.t
    val max_elt_opt : t -> AbstractionMap.AbstractNode.t option
    val choose : t -> AbstractionMap.AbstractNode.t
    val choose_opt : t -> AbstractionMap.AbstractNode.t option
    val split : AbstractionMap.AbstractNode.t -> t -> t * bool * t
    val find :
      AbstractionMap.AbstractNode.t -> t -> AbstractionMap.AbstractNode.t
    val find_opt :
      AbstractionMap.AbstractNode.t ->
      t -> AbstractionMap.AbstractNode.t option
    val find_first :
      (AbstractionMap.AbstractNode.t -> bool) ->
      t -> AbstractionMap.AbstractNode.t
    val find_first_opt :
      (AbstractionMap.AbstractNode.t -> bool) ->
      t -> AbstractionMap.AbstractNode.t option
    val find_last :
      (AbstractionMap.AbstractNode.t -> bool) ->
      t -> AbstractionMap.AbstractNode.t
    val find_last_opt :
      (AbstractionMap.AbstractNode.t -> bool) ->
      t -> AbstractionMap.AbstractNode.t option
    val of_list : AbstractionMap.AbstractNode.t list -> t
  end

(** Maps with abstract nodes as keys *)     
module AbstractNodesMap :
  sig
    type +'a t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : AbstractNodeSet.t -> 'a t -> bool
    val add : AbstractNodeSet.t -> 'a -> 'a t -> 'a t
    val update :
      AbstractNodeSet.t -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : AbstractNodeSet.t -> 'a -> 'a t
    val remove : AbstractNodeSet.t -> 'a t -> 'a t
    val merge :
      (AbstractNodeSet.t -> 'a option -> 'b option -> 'c option) ->
      'a t -> 'b t -> 'c t
    val union :
      (AbstractNodeSet.t -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (AbstractNodeSet.t -> 'a -> unit) -> 'a t -> unit
    val fold : (AbstractNodeSet.t -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (AbstractNodeSet.t -> 'a -> bool) -> 'a t -> bool
    val exists : (AbstractNodeSet.t -> 'a -> bool) -> 'a t -> bool
    val filter : (AbstractNodeSet.t -> 'a -> bool) -> 'a t -> 'a t
    val partition : (AbstractNodeSet.t -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (AbstractNodeSet.t * 'a) list
    val min_binding : 'a t -> AbstractNodeSet.t * 'a
    val min_binding_opt : 'a t -> (AbstractNodeSet.t * 'a) option
    val max_binding : 'a t -> AbstractNodeSet.t * 'a
    val max_binding_opt : 'a t -> (AbstractNodeSet.t * 'a) option
    val choose : 'a t -> AbstractNodeSet.t * 'a
    val choose_opt : 'a t -> (AbstractNodeSet.t * 'a) option
    val split : AbstractNodeSet.t -> 'a t -> 'a t * 'a option * 'a t
    val find : AbstractNodeSet.t -> 'a t -> 'a
    val find_opt : AbstractNodeSet.t -> 'a t -> 'a option
    val find_first :
      (AbstractNodeSet.t -> bool) -> 'a t -> AbstractNodeSet.t * 'a
    val find_first_opt :
      (AbstractNodeSet.t -> bool) -> 'a t -> (AbstractNodeSet.t * 'a) option
    val find_last :
      (AbstractNodeSet.t -> bool) -> 'a t -> AbstractNodeSet.t * 'a
    val find_last_opt :
      (AbstractNodeSet.t -> bool) -> 'a t -> (AbstractNodeSet.t * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (AbstractNodeSet.t -> 'a -> 'b) -> 'a t -> 'b t
  end
     
(** Given a graph and a destination node compute an abstraction function *)
val findAbstraction :
  Graph.t -> Graph.Vertex.t -> AbstractionMap.abstractionMap

(** Given a concrete graph, an abstraction function, and a abstrId of an
   abstract node to split, tries to refine the abstraction leveraging
   the given path if possible *)
val refineForFailures :
  Graph.t ->
  AbstractionMap.abstractionMap ->
  AbstractionMap.abstrId ->
  AbstractionMap.abstrId list -> AbstractionMap.abstractionMap

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
