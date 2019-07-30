open Batteries

module IntMap = Map.Make (struct
  type t = int

  let compare = compare
end)

module IntSet = Set.Make (struct
    type t = int

    let compare = compare
  end)

module StringMap = Map.Make (struct
    type t = string

    let compare = String.compare
  end)

module StringSet = Set.Make (struct
  type t = String.t

  let compare = String.compare
end)

module StringSetSet = Set.Make (struct
  type t = StringSet.t

  let compare = StringSet.compare
end)
