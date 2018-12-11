open Unsigned
   
module AbstractNode :
sig
  include module type of AdjGraph.VertexSet
  val toSet : t -> AdjGraph.VertexSet.t
  val fromSet : AdjGraph.VertexSet.t -> t
  val printAbstractNode : t -> string
  val randomSplit : t -> t * t
  end
module UInts : sig type t = Integer.t val compare : t -> t -> int end

type abstrId = Integer.t
module GroupMap : BatMap.S with type key = abstrId

(** The type of abstraction maps *)
type abstractionMap

(** Given an abstraction map and a node, returns its abstraction. 
    Raises [Not_found] *)
val getGroup : abstractionMap -> AdjGraph.Vertex.t -> AbstractNode.t

(** Given an abstraction map and a node, returns the id of the
   abstract node it belongs to.  
   Raises [Not_found] *)
val getId : abstractionMap -> AdjGraph.Vertex.t -> abstrId
  
(** Given an abstraction map and the id of an abstract node, returns the abstract node.
    Raises [Not_found] *)
val getGroupById : abstractionMap -> abstrId -> AbstractNode.t

(** Given an abstraction and an abstract node returns a concrete node
   that acts as the representative of all concrete nodes in this group *)
val getGroupRepresentative: abstractionMap -> AbstractNode.t -> AdjGraph.Vertex.t

(** Given an abstraction and the id of an abstract node returns a concrete node
   that acts as the representative of all concrete nodes in this group *)
val getGroupRepresentativeId: abstractionMap -> abstrId -> AdjGraph.Vertex.t
  
(** Given an abstraction and an abstract node returns a unique id for this abstract node*)
val getGroupId: abstractionMap -> AbstractNode.t -> abstrId
  
(** Split the given set of nodes to a new abstract node and return the new abstraction*)
val split : abstractionMap -> AbstractNode.t -> abstractionMap

(** Given an abstraction returns the abstract groups *)
val getAbstractGroups : abstractionMap -> (GroupMap.key * AbstractNode.t) list

(** [printAbstractGroups f sep] returns a string with the abstract
   groups created by [f], separated by [sep] *)
val printAbstractGroups: abstractionMap -> string -> string

(** Given a graph, creates an initial abstraction *)
val createAbstractionMap : AdjGraph.t -> abstractionMap

val fold: (AbstractNode.t -> 'a -> 'a) -> abstractionMap -> 'a -> 'a

(** Returns the number of abstract nodes *)
val size: abstractionMap -> int

val copyMap: abstractionMap -> abstractionMap
  
(** [normalize f] returns f with indices reordered to be contigious*)
val normalize: abstractionMap -> abstractionMap
  
