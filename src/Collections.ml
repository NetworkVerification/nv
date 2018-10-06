open Syntax

module StringMap = Map.Make (struct
  type t = string

  let compare = String.compare
end)

module VarMap = Map.Make (struct
  type t = Var.t

  let compare = compare
end)

module VarSet = Set.Make (struct
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


let groupKeysByValue (umap: ('a, 'b) BatMap.t) : ('a BatSet.t) BatSet.t =
  let reverseMap : ('b, 'a BatSet.t) BatMap.t =
    BatMap.foldi (fun u vhat acc ->
        BatMap.modify_opt vhat (fun us -> match us with
                                          | None -> Some (BatSet.singleton u)
                                          | Some us -> Some (BatSet.add u us)) acc)
                 umap BatMap.empty in
  BatMap.fold (fun v acc -> BatSet.add v acc)
              reverseMap BatSet.empty
