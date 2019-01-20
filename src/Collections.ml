open Syntax

module StringMap = BatMap.Make (struct
  type t = string

  let compare = String.compare
end)

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

module ExpSet = Set.Make (struct
    type t = exp

    let compare = compare_es
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
  let buf = Buffer.create 500 in
  let rec loop ls =
    match ls with
    | [] -> ()
    | [l] -> Buffer.add_string buf (printer l)
    | l :: ls ->
       Buffer.add_string buf (printer l);
       Buffer.add_string buf sep;
       loop ls 
  in
  Buffer.add_string buf first;
  loop ls;
  Buffer.add_string buf last;
  Buffer.contents buf
