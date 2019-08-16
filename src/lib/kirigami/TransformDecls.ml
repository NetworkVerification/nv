open Batteries
open Nv_lang
open Nv_datastructures
open Syntax

let add_init_branch (aux: AdjGraph.Vertex.t) (base: AdjGraph.Vertex.t) (b: branches) : branches = 
  (* TODO: add a branch with pattern aux and expression (init v) *)
  b

(* Return true if the expression is a function which accepts a node as an input *)
let is_node_func (e: Syntax.exp) : bool =
    let { argty; _ } = Syntax.deconstructFun e in
    match argty with
    | Some TNode -> true
    | _ -> false

(* Pass in the original init Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * a single parameter of type tnode.
 *)
let transform_init (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  (* check that e has the right format *)
  if not (is_node_func e) then 
    failwith "Tried to transform init for partitioning, but the type is not (TNode -> A)!"
  else
    let { inputs; outputs;_ } : OpenAdjGraph.t = ograph in
    let default_branch = addBranch PWild e emptyBranch in
    let input_branches = AdjGraph.VertexMap.fold add_init_branch inputs default_branch in
    let output_branches = AdjGraph.VertexMap.fold add_init_branch outputs input_branches in
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
