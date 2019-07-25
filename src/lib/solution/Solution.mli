open Nv_datastructures.AdjGraph
open Nv_core.Collections

type t =
  { symbolics: Nv_core.Syntax.value VarMap.t
  ; labels: Nv_core.Syntax.value VertexMap.t
  ; assertions: bool VertexMap.t option }

val print_solution : t -> unit
