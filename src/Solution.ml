open Graph

module StringMap = Map.Make (struct
  type t = string

  let compare = String.compare
end)

type t =
  { symbolics: Syntax.value option StringMap.t
  ; labels: Syntax.value option VertexMap.t
  ; assertions: bool VertexMap.t option }
