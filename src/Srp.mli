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

val simulate_declarations : declarations -> Solution.t

val simulate_declarations_bound :
  declarations -> int -> Solution.t * queue
  
val declarations_to_srp : Syntax.declaration list -> throw_requires:bool ->
                            srp * Syntax.closure * Syntax.value Collections.StringMap.t
