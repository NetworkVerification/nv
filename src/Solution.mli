open AdjGraph
open Collections

type t =
  { symbolics: Syntax.value StringMap.t
  ; labels: Syntax.value VertexMap.t
  ; assertions: bool VertexMap.t option }

val print_solution : t -> unit
