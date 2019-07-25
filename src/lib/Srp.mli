exception Simulation_error of string

exception Require_false

type srp =
  { graph: Nv_datastructures.AdjGraph.t
  ; trans: Nv_core.Syntax.closure
  ; merge: Nv_core.Syntax.closure
  ; assertion: Nv_core.Syntax.closure option }

type queue = Nv_datastructures.AdjGraph.Vertex.t Nv_datastructures.QueueSet.queue

val simulate_net : Nv_core.Syntax.network -> Nv_solution.Solution.t

val simulate_net_bound :
  Nv_core.Syntax.network -> int -> Nv_solution.Solution.t * queue

val net_to_srp : Nv_core.Syntax.network -> throw_requires:bool ->
                            srp * Nv_core.Syntax.closure * Nv_core.Syntax.value Nv_core.Collections.VarMap.t
