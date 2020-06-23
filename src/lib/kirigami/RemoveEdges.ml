open Batteries
open Nv_lang.Syntax
open Nv_datastructures.AdjGraph
open Nv_transformations
open SrpRemapping

let ty_transformer _ ty = Some ty

let pattern_transformer (_: Transformers.recursors) p _ = Some p

let value_transformer _ v = Some v

let exp_transformer (edges: edge list) (recursors: Transformers.recursors) e =
  let removeExp = recursors.recurse_exp in
  let in_edges p = match p with
    | PEdge (PNode u, PNode v) -> List.mem (u, v) edges
    | _ -> false
  in
  let update_branches old_bs =
    foldBranches (fun (p, e) new_bs -> begin
          if (in_edges p) then new_bs else addBranch p (removeExp e) new_bs
        end) emptyBranch old_bs
  in
  match e.e with
  | EMatch (e1, bs) ->
    let bs' = update_branches bs in
    Some (ematch (removeExp e1) (optimizeBranches bs'))
  | _ -> None

let map_back_transformer (_edges: edge list) _ _ v _ = Some v

let mask_transformer _ _ v _ = Some v

let make_toplevel (edges: edge list) (toplevel_transformer : 'a Transformers.toplevel_transformer) =
  toplevel_transformer ~name:"Delete Edges"
    ty_transformer pattern_transformer value_transformer
    (exp_transformer edges) (map_back_transformer edges) mask_transformer

let remap_declarations edges = make_toplevel edges Transformers.transform_declarations
let remap_net edges = make_toplevel edges Transformers.transform_network
let remap_srp edges = make_toplevel edges Transformers.transform_srp
