open Syntax

module StringMap = RecordUtils.StringMap

module StringSet = BatSet.Make (struct
  type t = String.t

  let compare = String.compare
end)

module StringSetSet = BatSet.Make (struct
  type t = StringSet.t

  let compare = StringSet.compare
end)

module VarMap = Map.Make (struct
  type t = Var.t

  let compare = compare
end)

module VarSet = BatSet.Make (struct
  type t = Var.t

  let compare = Var.compare
end)

module TypeMap = Map.Make (struct
  type t = ty

  let compare = compare
end)

module ValueSet = Set.Make (struct
  type t = value

  let compare v1 v2 =
    let cfg = Cmdline.get_cfg () in
    if cfg.hashcons then v1.vtag - v2.vtag else compare v1 v2
end)

module ValueMap = Map.Make (struct
  type t = value

  let compare v1 v2 =
    let cfg = Cmdline.get_cfg () in
    if cfg.hashcons then v1.vtag - v2.vtag else compare v1 v2
end)

let printList (printer: 'a -> string) (ls: 'a list) (first : string)
              (sep : string) (last : string) =
  let rec loop ls =
    match ls with
    | [] -> ""
    | [l] -> printer l
    | l :: ls -> (printer l) ^ sep ^ (loop ls)
  in
  first ^ (loop ls) ^ last
