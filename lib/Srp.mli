open Collections
open Unsigned
open Solution
open Syntax

exception Simulation_error of string

exception Require_false

type srp =
  { graph: AdjGraph.t
  ; trans: Syntax.closure
  ; merge: Syntax.closure
  ; assertion: Syntax.closure option }

type queue = AdjGraph.Vertex.t QueueSet.queue

val simulate_net : Syntax.network -> Solution.t

val simulate_net_bound :
  Syntax.network -> int -> Solution.t * queue

val net_to_srp : Syntax.network -> throw_requires:bool ->
                            srp * Syntax.closure * Syntax.value Collections.VarMap.t
