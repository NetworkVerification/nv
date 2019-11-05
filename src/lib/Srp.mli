exception Simulation_error of string

exception Require_false

type srp =
  { graph: Nv_datastructures.AdjGraph.t
  ; trans: Nv_lang.Syntax.closure
  ; merge: Nv_lang.Syntax.closure
  ; assertion: Nv_lang.Syntax.closure option }

type queue = Nv_datastructures.AdjGraph.Vertex.t Nv_datastructures.QueueSet.queue

val simulate_net : Nv_lang.Syntax.network -> Nv_solution.Solution.t

val simulate_net_bound :
  Nv_lang.Syntax.network -> int -> Nv_solution.Solution.t * queue

val net_to_srp : Nv_lang.Syntax.network -> throw_requires:bool ->
                            srp * Nv_lang.Syntax.closure * Nv_lang.Syntax.value Nv_lang.Collections.VarMap.t
