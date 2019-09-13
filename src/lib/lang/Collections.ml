open Syntax
open Batteries
open Nv_datastructures
include Nv_utils.PrimitiveCollections

module VarMap = BetterMap.Make(Var)
module VarSet = BetterSet.Make(Var)

module TypeMap = BetterMap.Make (struct
    type t = ty

    let compare = compare
    let to_string = Printing.ty_to_string
  end)

module ValueSet = BetterSet.Make (struct
    type t = value

    let compare v1 v2 =
      let cfg = Cmdline.get_cfg () in
      if cfg.hashcons then v1.vtag - v2.vtag else compare v1 v2
    let to_string = Printing.value_to_string
  end)

module ValueMap = BetterMap.Make (struct
    type t = value

    let compare v1 v2 =
      let cfg = Cmdline.get_cfg () in
      if cfg.hashcons then v1.vtag - v2.vtag else compare v1 v2
    let to_string = Printing.value_to_string
  end)
;;

module ExpMap = BetterMap.Make (struct
    type t = exp

    let compare e1 e2 =
      let cfg = Cmdline.get_cfg () in
      if cfg.hashcons then e1.etag - e2.etag else
        compare e1 e2
    let to_string = Printing.exp_to_string
  end)

module ExpSet = BetterSet.Make (struct
    type t = exp

    let compare = compare_es
    let to_string = Printing.exp_to_string
  end)
