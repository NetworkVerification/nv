open Nv_datastructures.AdjGraph
open Nv_lang.Collections

type t =
  { symbolics: Nv_lang.Syntax.value VarMap.t
  ; labels: Nv_lang.Syntax.value VertexMap.t
  ; assertions: bool VertexMap.t option }

val print_solution : t -> unit
