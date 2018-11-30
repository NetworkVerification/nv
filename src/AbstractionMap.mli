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
module GroupMap :
  sig
    type key = UInts.t
    type 'a t = 'a Map.Make(UInts).t
    val empty : 'a t
    val is_empty : 'a t -> bool
    val mem : key -> 'a t -> bool
    val add : key -> 'a -> 'a t -> 'a t
    val update : key -> ('a option -> 'a option) -> 'a t -> 'a t
    val singleton : key -> 'a -> 'a t
    val remove : key -> 'a t -> 'a t
    val merge :
      (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
    val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t
    val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
    val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val for_all : (key -> 'a -> bool) -> 'a t -> bool
    val exists : (key -> 'a -> bool) -> 'a t -> bool
    val filter : (key -> 'a -> bool) -> 'a t -> 'a t
    val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t
    val cardinal : 'a t -> int
    val bindings : 'a t -> (key * 'a) list
    val min_binding : 'a t -> key * 'a
    val min_binding_opt : 'a t -> (key * 'a) option
    val max_binding : 'a t -> key * 'a
    val max_binding_opt : 'a t -> (key * 'a) option
    val choose : 'a t -> key * 'a
    val choose_opt : 'a t -> (key * 'a) option
    val split : key -> 'a t -> 'a t * 'a option * 'a t
    val find : key -> 'a t -> 'a
    val find_opt : key -> 'a t -> 'a option
    val find_first : (key -> bool) -> 'a t -> key * 'a
    val find_first_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val find_last : (key -> bool) -> 'a t -> key * 'a
    val find_last_opt : (key -> bool) -> 'a t -> (key * 'a) option
    val map : ('a -> 'b) -> 'a t -> 'b t
    val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t
  end

(** The type of abstraction maps *)
type abstractionMap
type abstrId = Integer.t

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
  

