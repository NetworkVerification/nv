open Nv_lang.Syntax
open Nv_datastructures.AdjGraph
open Nv_datastructures
open Nv_solution

(* A record for managing the input node information *)
type input_exp =
  { (* the associated original edge *)
    edge : E.t
  ; (* the variable associated with the input node *)
    var : Var.t
  ; (* the partition rank of the associated output *)
    rank : int
  ; (* the associated predicate expression: a function over attributes *)
    (* optional: if not given, then assumed to always hold *)
    preds : exp list
  }

(** A type for transforming the declarations over the old SRP
 ** to declarations for the new partitioned SRP.
 ** The nodes and edges maps help us to remap nodes and edges.
 ** If an old node or edge is not a value in the map,
 ** then we know it has been removed and we can drop it from
 ** the SRP.
 ** The predicates help us keep track of the `interface` predicates
 ** associated with a given new edge, since both inputs and outputs
 ** have associated predicates (required on the hypotheses and
 ** asserted on the output solutions, respectively).
 **
 ** Invariants:
 ** - every value in node_map and edge_map is a valid node or edge
 **   in the new SRP
 **)
type partitioned_srp =
  { (* the rank of the partitioned srp *)
    rank : int
  ; (* the number of nodes in the network *)
    nodes : int
  ; (* the edges in the network *)
    edges : Edge.t list
  ; (* keys are old nodes, values are Some new node or None *)
    node_map : Vertex.t option VertexMap.t
  ; (* keys are old edges, values are Some new edge or None *)
    edge_map : Edge.t option EdgeMap.t
  ; (* Maps from base nodes to their inputs and outputs *)
    (* the predicate applies to the input node as a `require`
     * on the hypothesis symbolic variable, and to the
     * output node as an `assert` on the solution
     *)
    inputs : input_exp list VertexMap.t
  ; outputs : (Edge.t * exp list) list VertexMap.t
  }

(** Return the number of nodes in the global network. *)
val get_global_nodes : partitioned_srp -> int

(** Return the list of old nodes in the network in order of how they were remapped, i.e.
 ** the 0th element of the list remaps to node 0, the 1st remaps to node 1 and so on. *)
val get_old_nodes : partitioned_srp -> int list

(** Return a string representation of the partitioned SRP. *)
val string_of_partitioned_srp : partitioned_srp -> string

(** Map a function over the inputs and outputs of the partitioned SRP.
 ** The function should take an edge as an argument and a boolean as its second argument;
 ** the boolean will be true for inputs and false for outputs. *)
val map_predicates : (Edge.t -> bool -> exp) -> partitioned_srp -> partitioned_srp

(** Create a list of partitioned SRP structures,
 * where each structure represents one partition's topological structure
 * for each possible partition in the given declarations.
*)
val partition_declarations : declarations -> partitioned_srp list
