open Graph

module StringMap = Map.Make (struct
  type t = string

  let compare = String.compare
end)

type t =
  { symbolics: Syntax.value StringMap.t
  ; labels: Syntax.value VertexMap.t
  ; assertions: bool VertexMap.t option }
