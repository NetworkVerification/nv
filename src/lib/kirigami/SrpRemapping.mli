open Nv_lang.Syntax
open Nv_datastructures.AdjGraph
open Nv_datastructures
open Nv_solution

(* A record for managing the input node information *)
type input_exp =
  { (* the associated original edge *)
    edge : E.t
  ; (* the variables associated with the input node *)
    var_names : Var.t list
  ; (* the partition rank of the associated output *)
    rank : int
  ; (* the associated predicate expression: a function over attributes *)
    (* optional: if not given, then assumed to always hold *)
    preds : exp list
  }

val edge_to_hyp : E.t -> Var.t

val is_hyp_var : E.t -> Var.t -> bool

val var_to_edge : Var.t -> E.t option

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
 **)
type partitioned_srp =
  { (* the rank of the partitioned srp *)
    rank : int
  ; (* the nodes in the network *)
    nodes : Vertex.t list
  ; (* the edges in the network *)
    edges : Edge.t list
  ; (* list of cut nodes in the monolithic network *)
    cut_nodes : Vertex.t list
  ; (* Maps from base nodes to their inputs and outputs *)
    (* the predicate applies to the input node as a `require`
     * on the hypothesis symbolic variable, and to the
     * output node as an `assert` on the solution
     *)
    inputs : input_exp list VertexMap.t
  ; outputs : (Edge.t * exp list) list VertexMap.t
  }

val get_cross_edges : partitioned_srp -> edge list

(** Return a string representation of the partitioned SRP. *)
val string_of_partitioned_srp : partitioned_srp -> string

(** Map a function over the inputs and outputs of the partitioned SRP.
 ** The function should take an edge as an argument and a list of predicates as its second argument.
 **)
val map_predicates
  :  (Edge.t -> exp list -> exp list)
  -> partitioned_srp
  -> partitioned_srp

(** Create a list of partitioned SRP structures,
 * where each structure represents one partition's topological structure
 * for each possible partition in the given declarations.
*)
val partition_declarations : ?which:int BatSet.t option -> declarations -> partitioned_srp list
