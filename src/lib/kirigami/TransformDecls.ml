open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax

let node_to_pat node =
  exp_to_pattern (e_val (vnode node))

let edge_to_pat edge =
  exp_to_pattern (e_val (vedge edge))

let amatch v t b =
  (ematch (aexp (evar v, t, Span.default)) b)

(* Pass in the original init Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * a single parameter of type tnode.
 *)
let transform_init (e: Syntax.exp) (interfaces: OpenAdjGraph.interfaces_alt) (input_exps: Syntax.exp EdgeMap.t) : Syntax.exp =
  let { inputs; outputs; _ } : OpenAdjGraph.interfaces_alt = interfaces in
  let node_var = Var.fresh "node" in
  let add_init_branch u v = 
    (* if the edge is present in the interface set, then use the specified expression;
     * this should be true only for the input edges since input_exps lists input~base edges *)
    let exp = match EdgeMap.Exceptionless.find (u, v) input_exps with 
    | Some exp -> exp
    (* output case: make the init the same as the base node *)
    | None -> (eapp e (e_val (vnode v)))
    in
    let node_pattern = node_to_pat u in
    addBranch node_pattern exp
  in
  (* the default branch runs (original_init node), where original_init = e *)
  let default_branch = addBranch PWild (eapp e (evar node_var)) emptyBranch in
  let input_branches = VertexMap.fold add_init_branch inputs default_branch in
  let output_branches = VertexMap.fold add_init_branch outputs input_branches in
  (* the returned expression should be a function that takes a node as input with the following body:
   * a match with node as the exp and output_branches as the branches *)
    wrap e (lam node_var (amatch node_var (Some TNode) output_branches))

(* Pass in the original trans Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * two parameters of types tedge and attribute
 *)
let transform_trans (e: Syntax.exp) (intf: OpenAdjGraph.interfaces_alt) : Syntax.exp =
  (* new function argument *)
  let edge_var = Var.fresh "edge" in
  let x_var = Var.fresh "x" in
  let { inputs; outputs; outs_broken } : OpenAdjGraph.interfaces_alt = intf in
  let in_trans_branch k v b = (* branches for in~base edges: identity function *)
    let edge_pat = edge_to_pat (k, v) in
    (* return the identity function *)
    (* let avar = Var.fresh "a" in *)
    (* let in_exp = (lam avar (evar avar)) in *)
    addBranch edge_pat (evar x_var) b
  in
  let out_trans_branch k v b = (* branches for base~out edges: perform original trans for full edge *)
    let edge_pat = edge_to_pat (v, k) in
    (* recover the old edge from the OpenAdjGraph's broken edges *)
    let old_edge = VertexMap.find k outs_broken in
    let edge_val = e_val (vedge old_edge) in
    (* call the original expression using the old edge;
     * this needs to be partially evaluated since the old edge doesn't exist anymore,
     * so the compiler will complain the edge isn't supposed to be mentioned
     *)
    let out_exp = (eapp (eapp e edge_val) (evar x_var)) in
    addBranch edge_pat out_exp b 
  in
  (* the default branch runs (original_trans edge), where original_trans = e *)
  let orig_trans = (apps e [(evar edge_var); (evar x_var)]) in
  let default_branch = addBranch PWild orig_trans emptyBranch in
  let input_branches = VertexMap.fold in_trans_branch inputs default_branch in
  let output_branches = VertexMap.fold out_trans_branch outputs input_branches in
    wrap e (lams [edge_var; x_var] (amatch edge_var (Some TEdge) output_branches))

let merge_branch (input: bool) (n: Vertex.t) (_: Vertex.t) (b: branches) : branches =
  let a1 = Var.fresh "a1" in
  let a2 = Var.fresh "a2" in
  let node_pat = node_to_pat n in
  (* create a function that takes 2 attributes and returns either the first (input case)
   * or the second (output case)
   *)
  let merge_exp = (lams [a1; a2] (if input then (evar a1) else (evar a2))) in 
  addBranch node_pat merge_exp b

let transform_merge (e: Syntax.exp) (intf: OpenAdjGraph.interfaces_alt) : Syntax.exp =
  let node_var = Var.fresh "node" in
  let { outputs; _ } : OpenAdjGraph.interfaces_alt = intf in
  let default_branch =
    addBranch PWild (eapp e (evar node_var)) emptyBranch
  in
  (* let input_branches = VertexMap.fold (merge_branch true) inputs default_branch in *)
  let output_branches = VertexMap.fold (merge_branch false) outputs default_branch in
    wrap e (lam node_var (amatch node_var (Some TNode) output_branches))

(* Apply the predicate test on the solution for node n *)
let assert_branch (x: var) (n: Vertex.t) (pred: exp) (b: branches) : branches =
  let node_pat = node_to_pat n in
  addBranch node_pat (eapp pred (evar x)) b 

let transform_assert (e: Syntax.exp option) (intf: OpenAdjGraph.interfaces_alt) (output_preds: exp VertexMap.t) : Syntax.exp option =
    let { inputs; outputs; _ } : OpenAdjGraph.interfaces_alt = intf in
    let node_var = Var.fresh "node" in
    let soln_var = Var.fresh "x" in
    let etrue = e_val (vbool true) in
    let e = match e with
    | Some e -> (apps e [(evar node_var); (evar soln_var)])
    | None -> etrue
    in
    let default_branch = addBranch PWild e emptyBranch
    in
    (* re-map every output to point to its corresponding predicate *)
    let outputs_to_preds = VertexMap.mapi (fun o _b -> (VertexMap.find o output_preds)) outputs
    in
    let output_branches = VertexMap.fold (assert_branch soln_var) outputs_to_preds default_branch in
    let input_branches = VertexMap.fold (fun innode _ b -> addBranch (node_to_pat innode) etrue b) inputs output_branches in
    let match_exp = amatch node_var (Some TNode) input_branches in
    Some (wrap e (lams [node_var; soln_var] match_exp))

