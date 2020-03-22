open Nv_lang
open Nv_datastructures

exception Simulation_error of string

exception Require_false

type srp =
  { graph: AdjGraph.t
  ; trans: Syntax.closure
  ; merge: Syntax.closure
  ; assertion: Syntax.closure option }

type queue = AdjGraph.Vertex.t QueueSet.queue

(* val simulate_net : Syntax.network -> Nv_solution.Solution.t
 *
 * val simulate_net_bound :
 *   Syntax.network -> int -> Nv_solution.Solution.t * queue *)

val simulate_solve :
  AdjGraph.t -> Syntax.env -> Syntax.solve -> Syntax. value AdjGraph.VertexMap.t

val net_to_srp : Syntax.network -> throw_requires:bool ->
                            srp * Syntax.closure * Syntax.value Collections.VarMap.t
