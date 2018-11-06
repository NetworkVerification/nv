(** The type of networks *)
type network =
  { attr_type : Syntax.ty;
    init      : Syntax.exp;
    trans     : Syntax.exp;
    merge     : Syntax.exp;
    assertion : Syntax.exp;
    graph     : Graph.t;
  }

(** The type of network prefixes *)
module Prefix : Map.OrderedType with type t = Integer.t * Integer.t

module PrefixSet : BatSet.S with type elt = Prefix.t

module PrefixMap : BatMap.S with type key = Prefix.t

module PrefixSetSet : BatSet.S with type elt = PrefixSet.t
     
val printPrefix : Prefix.t -> string

val printPrefixes : PrefixSet.t -> string

(** [relevantPrefixes assertTable] returns the prefixes that are used by the
   assertion function*)
val relevantPrefixes: (Integer.t, Syntax.exp) Hashtbl.t -> PrefixSet.t

(** [partialEvalInit network] returns a table that maps each node to
   its initial state function *)
val partialEvalInit: network -> (Integer.t, Syntax.exp) Hashtbl.t

(** [partialEvalAssert network] returns a table that maps each node to
   its assertion function *)
val partialEvalAssert: network -> (Integer.t, Syntax.exp) Hashtbl.t
  
(** [findInitialSlices n] returns a map from prefix to set of nodes,
   with the property that each node in the set announces this
   prefix. *)
val findInitialSlices: (Integer.t, Syntax.exp) Hashtbl.t ->
                       (Graph.VertexSet.t) PrefixMap.t

val groupPrefixesByVertices: Graph.VertexSet.t PrefixMap.t -> PrefixSetSet.t
