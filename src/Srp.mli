open Collections
open Unsigned
open Solution
open Syntax

exception Simulation_error of string

exception Require_false

type queue = Graph.Vertex.t QueueSet.queue

val simulate_declarations : declarations -> Solution.t

val simulate_declarations_bound :
  declarations -> int -> Solution.t * queue
