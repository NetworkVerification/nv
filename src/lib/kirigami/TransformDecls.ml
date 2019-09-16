open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax

(* Return true if the expression is a function which accepts the given arg type as an input *)
let is_argty_func (e: Syntax.exp) (at: Syntax.ty) : bool =
    let { argty; _ } = Syntax.deconstructFun e in
    (* wrap the given arg type in an option, since functions don't always specify the argtype *)
    (* TODO: what does it mean if the argty is None? *)
    argty == Some at

(* Add a new branch to the given set of branches where the given aux node is added as a pattern to the
 * branch, and its resulting expression is the given init expression applied with the given base node.
 *)
let add_init_branch (init: Syntax.exp) (aux: Vertex.t) (base: Vertex.t) (b: branches) : branches = 
  let node_pattern = exp_to_pattern (e_val (vnode aux)) in
  let init_exp = eapp init (e_val (vnode base)) in
  addBranch node_pattern init_exp b

(* Pass in the original init Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * a single parameter of type tnode.
 *)
let transform_init (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  (* check that e has the right format *)
  if not (is_argty_func e TNode) then 
    failwith "Tried to transform init for partitioning, but the type is not (TNode -> A)!"
  else
    (* new function argument *)
    let node_var = Var.create "node" in
    (* curry init impl into add_init_branch *)
    let init_branch k v = add_init_branch e k v in
    let { inputs; outputs;_ } : OpenAdjGraph.t = ograph in
    (* the default branch runs (original_init node), where original_init = e *)
    let default_branch = addBranch PWild (eapp e (evar node_var)) emptyBranch in
    let input_branches = VertexMap.fold init_branch inputs default_branch in
    let output_branches = VertexMap.fold init_branch outputs input_branches in
    (* the returned expression should be a function that takes a node as input with the following body:
     * a match with node as the exp and output_branches as the branches *)
      lam node_var (ematch (evar node_var) output_branches)

(* Pass in the original trans Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * two parameters of types tedge and attribute
 *)
let transform_trans (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  if not (is_argty_func e TEdge) then 
    failwith "Tried to transform trans for partitioning, but the type is not (TEdge -> A -> A)!"
  else
    (* new function argument *)
    let edge_var = Var.create "edge" in
    let { inputs; outputs; _ } : OpenAdjGraph.t = ograph in
    let in_trans_branch k v b = (* branches for in~base edges: identity function *)
      let edge_pat = exp_to_pattern (e_val (vedge (k, v))) in
      (* return the identity function *)
      let avar = Var.create "a" in
      let in_exp = (lam avar (evar avar)) in
      addBranch edge_pat in_exp b
    in
    let out_trans_branch k v b = (* branches for base~out edges: perform original trans for full edge *)
      let edge_pat = exp_to_pattern (e_val (vedge (v, k))) in
      (* recover the old edge from the OpenAdjGraph's broken edges *)
      let old_edge = OpenAdjGraph.broken_edge ograph k in
      let edge_val = e_val (vedge old_edge) in
      (* call the original expression using the old edge *)
      let out_exp = (eapp e edge_val) in
      addBranch edge_pat out_exp b 
    in
    (* the default branch runs (original_trans edge), where original_trans = e *)
    let default_branch = addBranch PWild (eapp e (evar edge_var)) emptyBranch in
    let input_branches = VertexMap.fold in_trans_branch inputs default_branch in
    let output_branches = VertexMap.fold out_trans_branch outputs input_branches in
      lam edge_var (ematch (evar edge_var) output_branches)

let merge_branch (input: bool) (n: Vertex.t) (_: Vertex.t) (b: branches) : branches =
  let a1 = Var.create "a1" in
  let a2 = Var.create "a2" in
  let node_pat = exp_to_pattern (e_val (vnode n)) in
  (* create a function that takes 2 attributes and returns either the first (input case)
   * or the second (output case)
   *)
  let merge_exp = (lams [a1; a2] (if input then (evar a1) else (evar a2))) in 
  addBranch node_pat merge_exp b

let transform_merge (e: Syntax.exp) (ograph: OpenAdjGraph.t) : Syntax.exp =
  if not (is_argty_func e TNode) then
    failwith "Tried to transform merge for partitioning, but the type is not (TNode -> A -> A -> A)!"
  else
    let node_var = Var.create "node" in
    let OpenAdjGraph.{ inputs; outputs; _ } = ograph in
    let default_branch =
      addBranch PWild e emptyBranch
    in
    let input_branches = VertexMap.fold (merge_branch true) inputs default_branch in
    let output_branches = VertexMap.fold (merge_branch false) outputs input_branches in
      lam node_var (ematch (evar node_var) output_branches)
