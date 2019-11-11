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
  (* argty == Some at *)
  (* FIXME: this check doesn't seem to be working *)
  true

let amatch v t b =
  (ematch (aexp (evar v, t, Span.default)) b)

(* Pass in the original init Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * a single parameter of type tnode.
 *)
let transform_init (e: Syntax.exp) (interfaces: OpenAdjGraph.interfaces) (input_exps: Syntax.exp EdgeMap.t) : Syntax.exp =
  (* check that e has the right format *)
  if not (is_argty_func e TNode) then 
    let () = Printf.printf "%s" (Printing.ty_to_string (Option.get e.ety)) in
  failwith "Tried to transform init for partitioning, but the type is not (TNode -> A)!"
  else
  (* new function argument *)
  let node_var = Var.fresh "node" in
  let add_init_branch u v = 
    (* if the edge is present in the interface set, then use the specified expression;
     * this should be true only for the input edges *)
    (* input_exps lists base-base edges, so we need to convert from output-base or input-base *)
    let exp = match EdgeMap.Exceptionless.find (u, v) input_exps with 
    | Some exp -> exp
    | None -> (eapp e (e_val (vnode v)))
    in
    let node_pattern = exp_to_pattern (e_val (vnode u)) in
    addBranch node_pattern exp
  in
  let { inputs; outputs; _ } : OpenAdjGraph.interfaces = interfaces in
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
let transform_trans (e: Syntax.exp) (intf: OpenAdjGraph.interfaces) : Syntax.exp =
  if not (is_argty_func e TEdge) then 
    let () = Printf.printf "%s" (Printing.ty_to_string (Option.get e.ety)) in
  failwith "Tried to transform trans for partitioning, but the type is not (TEdge -> A -> A)!"
  else
  (* new function argument *)
  let edge_var = Var.fresh "edge" in
  let { inputs; outputs; _ } : OpenAdjGraph.interfaces = intf in
  let in_trans_branch k v b = (* branches for in~base edges: identity function *)
    let edge_pat = exp_to_pattern (e_val (vedge (k, v))) in
    (* return the identity function *)
    let avar = Var.fresh "a" in
    let in_exp = (lam avar (evar avar)) in
    addBranch edge_pat in_exp b
  in
  let out_trans_branch k v b = (* branches for base~out edges: perform original trans for full edge *)
    let edge_pat = exp_to_pattern (e_val (vedge (v, k))) in
    (* recover the old edge from the OpenAdjGraph's broken edges *)
    let old_edge = OpenAdjGraph.broken_edge intf k in
    let edge_val = e_val (vedge old_edge) in
    (* call the original expression using the old edge;
     * this needs to be partially evaluated since the old edge doesn't exist anymore,
     * so the compiler will complain the edge isn't supposed to be mentioned
     *)
    let out_exp = (eapp e edge_val) in
    addBranch edge_pat out_exp b 
  in
  (* the default branch runs (original_trans edge), where original_trans = e *)
  let default_branch = addBranch PWild (eapp e (evar edge_var)) emptyBranch in
  let input_branches = VertexMap.fold in_trans_branch inputs default_branch in
  let output_branches = VertexMap.fold out_trans_branch outputs input_branches in
    wrap e (lam edge_var (amatch edge_var (Some TEdge) output_branches))

let merge_branch (input: bool) (n: Vertex.t) (_: Vertex.t) (b: branches) : branches =
  let a1 = Var.fresh "a1" in
  let a2 = Var.fresh "a2" in
  let node_pat = exp_to_pattern (e_val (vnode n)) in
  (* create a function that takes 2 attributes and returns either the first (input case)
   * or the second (output case)
   *)
  let merge_exp = (lams [a1; a2] (if input then (evar a1) else (evar a2))) in 
  addBranch node_pat merge_exp b

let transform_merge (e: Syntax.exp) (intf: OpenAdjGraph.interfaces) : Syntax.exp =
  if not (is_argty_func e TNode) then
    let () = Printf.printf "%s" (Printing.ty_to_string (Option.get e.ety)) in
  failwith "Tried to transform merge for partitioning, but the type is not (TNode -> A -> A -> A)!"
  else
  let node_var = Var.fresh "node" in
  let OpenAdjGraph.{ inputs; outputs; _ } = intf in
  let default_branch =
    addBranch PWild (eapp e (evar node_var)) emptyBranch
  in
  let input_branches = VertexMap.fold (merge_branch true) inputs default_branch in
  let output_branches = VertexMap.fold (merge_branch false) outputs input_branches in
    wrap e (lam node_var (amatch node_var (Some TNode) output_branches))

(* Apply the predicate test on the solution for node n *)
let assert_branch (x: var) (n: Vertex.t) (pred: exp) (b: branches) : branches =
  let node_pat = exp_to_pattern (e_val (vnode n)) in
  addBranch node_pat (eapp pred (evar x)) b 

let transform_assert (e: Syntax.exp option) (intf: OpenAdjGraph.interfaces) (edge_preds: exp EdgeMap.t) : Syntax.exp option =
  if not (Option.is_none e || is_argty_func (Option.get e) TNode) then
    failwith "Tried to transform assert for partitioning, but the type is not (TNode -> A -> Bool)!"
  else
    let { inputs; outputs; _ } : OpenAdjGraph.interfaces = intf in
    let node_var = Var.fresh "node" in
    let soln_var = Var.fresh "x" in
    let etrue = e_val (vbool true) in
    let e = match e with
    | Some e -> (apps e [(evar node_var); (evar soln_var)])
    | None -> etrue
    in
    let default_branch = addBranch PWild e emptyBranch
    in
    (* helper function to associate an output with an edge predicate *)
    let get_output_pred n =
      let edge = OpenAdjGraph.broken_edge intf n in
      EdgeMap.find edge edge_preds
    in
    (* re-map every output to point to its corresponding predicate *)
    let outputs_to_preds = VertexMap.mapi (fun o _b -> (get_output_pred o)) outputs
    in
    let output_branches = VertexMap.fold (assert_branch soln_var) outputs_to_preds default_branch in
    let input_branches = VertexMap.fold (fun innode _ b -> addBranch (exp_to_pattern (e_val (vnode innode))) etrue b) inputs output_branches in
    let match_exp = amatch node_var (Some TNode) input_branches in
    Some (wrap e (lams [node_var; soln_var] match_exp))

