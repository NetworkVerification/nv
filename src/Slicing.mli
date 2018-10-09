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
type prefix = Unsigned.UInt32.t * Unsigned.UInt32.t

(** [relevantPrefixes assertTable] returns the prefixes that are used by the
   assertion function*)
val relevantPrefixes: (Unsigned.UInt32.t, Syntax.exp) Hashtbl.t -> prefix BatSet.t

(** [partialEvalInit network] returns a table that maps each node to
   its initial state function *)
val partialEvalInit: network -> (Unsigned.UInt32.t, Syntax.exp) Hashtbl.t

(** [partialEvalAssert network] returns a table that maps each node to
   its assertion function *)
val partialEvalAssert: network -> (Unsigned.UInt32.t, Syntax.exp) Hashtbl.t
  
(** [findInitialSlices n] returns a map from prefix to set of nodes,
   with the property that each node in the set announces this
   prefix. *)
val findInitialSlices: (Unsigned.UInt32.t, Syntax.exp) Hashtbl.t ->
                       (prefix, Graph.Vertex.t BatSet.t) BatMap.t

