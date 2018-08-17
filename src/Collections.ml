open Syntax

module StringMap = Map.Make (struct
  type t = string

  let compare = String.compare
end)

module VarMap = Map.Make (struct
  type t = Var.t

  let compare = compare
end)

module TypeMap = Map.Make (struct
  type t = ty

  let compare = compare
end)

module ValueSet = Set.Make (struct
  type t = value

  let compare = compare
end)

module ValueMap = Map.Make (struct
  type t = value

  let compare = compare
end)
