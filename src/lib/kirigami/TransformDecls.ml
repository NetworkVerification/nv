open Batteries
open Nv_lang
open Nv_datastructures
open Syntax

let add_init_branch (b: branches) (aux: AdjGraph.Vertex.t) (base: AdjGraph.Vertex.t) : branches = 
  (* TODO: add a branch with pattern aux and expression (init v) *)
  b

let transform_init (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  let { inputs; outputs;_ } : OpenAdjGraph.t = ograph in
  let default_branch =
    addBranch PWild e emptyBranch
  in
  let input_branches = AdjGraph.VertexMap.fold (fun k v b -> b) inputs default_branch in
  let output_branches = AdjGraph.VertexMap.fold (fun k v b -> b) outputs input_branches in
  failwith "TODO"
  (* the returned expression should be a match with "node" as the exp and output_branches as the pattern *)
  (* DInit (ematch branches) *)

let transform_trans (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  let OpenAdjGraph.{ inputs; outputs;_ } = ograph in
  let default_branch =
    addBranch PWild e emptyBranch
  in
  let _branches =
    default_branch
  in
  failwith "TODO"
  (* DTrans (ematch branches) *)

let transform_merge (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  let OpenAdjGraph.{ inputs; outputs;_ } = ograph in
  let default_branch =
    addBranch PWild e emptyBranch
  in
  let _branches =
    default_branch
  in
  failwith "TODO"
  (* DMerge (ematch branches) *)
