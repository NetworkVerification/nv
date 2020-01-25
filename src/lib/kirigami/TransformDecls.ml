open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax

let node_to_exp n = e_val (vnode n)

let edge_to_exp e = e_val (vedge e)

let node_to_pat node =
  exp_to_pattern @@ node_to_exp node

let edge_to_pat edge =
  exp_to_pattern @@ edge_to_exp edge

let amatch v t b =
  (ematch (aexp (evar v, t, Span.default)) b)

(** Add match branches using the given map of old nodes to new nodes. *)
let match_of_node_map (m: Vertex.t option VertexMap.t) b =
  let add_node_branch old_node new_node branches =
    match new_node with
    | Some n -> addBranch (node_to_pat n) (node_to_exp old_node) branches
    | None -> branches
    (* if there is no new node, just map the old node to itself *)
      (* addBranch (node_to_pat old_node) (node_to_exp old_node) branches *)
  in
  VertexMap.fold add_node_branch m b

(** Add match branches using the given map of old edges to new edges. *)
let match_of_edge_map (m: Edge.t option EdgeMap.t) b =
  let add_edge_branch old_edge new_edge branches =
    match new_edge with
    | Some e -> addBranch (edge_to_pat e) (edge_to_exp old_edge) branches
    | None -> branches
  in
  EdgeMap.fold add_edge_branch m b

(* Pass in the original init Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * a single parameter of type tnode.
 * There are 3 transformations we do:
 * - add a new input node
 * - add a new output node
 * - map a new node to an old node
 *)
let transform_init
    (old: Syntax.exp)
    (interfaces: SrpRemapping.interface)
    (input_exps: Syntax.exp EdgeMap.t)
    (node_map: Vertex.t option VertexMap.t)
  : Syntax.exp =
  let { inputs; outputs } : SrpRemapping.interface = interfaces in
  let node_var = Var.fresh "node" in
  let add_init_branch u v = 
    (* if the edge is present in the interface set, then use the specified expression;
     * this should be true only for the input edges since input_exps lists input~base edges *)
    let exp = match EdgeMap.Exceptionless.find (u, v) input_exps with 
    | Some exp -> exp
    (* output case: make the init the same as the base node *)
    (* have to remap again here *)
    | None -> begin
        (* get the base node matching the given new node *)
        let ((old_base, _), m) = VertexMap.pop @@ VertexMap.filterv (fun n -> match n with
            | Some n -> n = v
            | None -> false) node_map in
        (* assert that this was the only node that matched *)
        assert (VertexMap.is_empty m);
        (* the output then applies the old init with the correct old base node *)
        (eapp old (node_to_exp old_base))
    end
    in addBranch (node_to_pat u) exp
  in
  (* let default_branch = addBranch PWild old emptyBranch in *)
  let base_map_match = match_of_node_map node_map emptyBranch in
  let base_branches = mapBranches (fun (pat,exp) -> (pat, eapp old exp)) base_map_match in
  let input_branches = VertexMap.fold add_init_branch inputs base_branches in
  let output_branches = VertexMap.fold add_init_branch outputs input_branches in
  (* the returned expression should be a function that takes a node as input with the following body:
   * a match with node as the exp and output_branches as the branches *)
    wrap old (lam node_var (amatch node_var (Some TNode) output_branches))

(* Pass in the original trans Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * two parameters of types tedge and attribute
 *)
let transform_trans (e: Syntax.exp) (intf: SrpRemapping.interface) (edge_map: Edge.t option EdgeMap.t) : Syntax.exp =
  (* new function argument *)
  let edge_var = Var.fresh "edge" in
  let x_var = Var.fresh "x" in
  let { inputs; outputs } : SrpRemapping.interface = intf in
  let in_trans_branch k v b = (* branches for in~base edges: identity function *)
    let edge_pat = edge_to_pat (k, v) in
    (* return the identity function *)
    (* let avar = Var.fresh "a" in *)
    (* let in_exp = (lam avar (evar avar)) in *)
    addBranch edge_pat (evar x_var) b
  in
  let out_trans_branch old_edge new_edge b =
    match new_edge with
    | Some new_edge -> begin
      let edge_pat = edge_to_pat new_edge in
      let edge_val = e_val (vedge old_edge) in
      (* call the original expression using the old edge;
       * this needs to be done after checking wellformedness since the old edge doesn't exist anymore,
       * so the compiler will complain the edge isn't supposed to be mentioned
       *)
      let out_exp = (eapp (eapp e edge_val) (evar x_var)) in
      addBranch edge_pat out_exp b 
    end
    | None -> b
  in
  (* the default branch runs (original_trans edge), where original_trans = e *)
  let orig_trans = (apps e [(evar edge_var); (evar x_var)]) in
  let default_branch = addBranch PWild orig_trans emptyBranch in
  (* input branches use the identity function *)
  let input_branches = VertexMap.fold in_trans_branch inputs default_branch in
  (* output branches perform the original transfer *)
  (* let output_branches = VertexMap.fold out_trans_branch outputs input_branches in *)
  (* use only the outputs in the edge map, since we've already added the inputs *)
  let filter_output_edges _ (maybe_edge: Edge.t option) : bool =
    let maybe_bool = Option.bind maybe_edge (fun (u, v) -> begin
    (* if there is some edge, look for it in outputs *)
      Option.map (fun u' -> u' = u) (VertexMap.Exceptionless.find v outputs)
    end) in
    Option.default false maybe_bool
  in
  let output_map = EdgeMap.filter filter_output_edges edge_map in
  let output_branches = EdgeMap.fold out_trans_branch output_map input_branches in
    wrap e (lams [edge_var; x_var] (amatch edge_var (Some TEdge) output_branches))

let merge_branch (n: Vertex.t) (_: Vertex.t) (b: branches) : branches =
  let a1 = Var.fresh "a1" in
  let a2 = Var.fresh "a2" in
  let node_pat = node_to_pat n in
  (* create a function that takes 2 attributes and returns the second one *)
  (* FIXME: this is a *brittle and dangerous solution*, since it relies on an
   * implementation detail to ignore the fact that we expect merge to be
   * commutative *)
  let merge_exp = (lams [a1; a2] (evar a2)) in
  addBranch node_pat merge_exp b

let transform_merge (e: Syntax.exp) (intf: SrpRemapping.interface) (node_map) : Syntax.exp =
  let node_var = Var.fresh "node" in
  let { outputs; _ } : SrpRemapping.interface = intf in
  (* let default_branch = addBranch PWild e emptyBranch in *)
  let map_match = match_of_node_map node_map emptyBranch in
  let base_branches = mapBranches (fun (pat, exp) -> (pat, eapp e exp)) map_match in
  let output_branches = VertexMap.fold merge_branch outputs base_branches in
    wrap e (lam node_var (amatch node_var (Some TNode) output_branches))

(* Apply the predicate test on the solution for node n *)
let assert_branch (x: var) (_basen, outn: Edge.t)  (pred: exp) (b: branches) : branches =
  let node_pat = node_to_pat outn in
  addBranch node_pat (eapp pred (evar x)) b 

let transform_assert
    (e: Syntax.exp option)
    (intf: SrpRemapping.interface)
    (output_preds: exp EdgeMap.t)
    node_map
  : Syntax.exp option =
  let { inputs; _ } : SrpRemapping.interface = intf in
  let node_var = Var.fresh "node" in
  let soln_var = Var.fresh "x" in
  let etrue = e_val (vbool true) in
  let apply_assert node soln = match e with
    | Some e -> (apps e [node; soln])
    | None -> etrue
  in
  (* If the old expression was Some, apply the assert with the given variables;
   * if it was None, simply create an expression evaluating to true *)
  (* let e = match e with
   *   | Some e -> (apps e [(evar node_var); (evar soln_var)])
   *   | None -> etrue
   * in *)
  (* Map the new base nodes to the old ones using the map_match *)
  let map_match = match_of_node_map node_map emptyBranch in
  let base_branches = mapBranches (fun (pat, exp) -> (pat, apply_assert exp (evar soln_var))) map_match in
  (* re-map every output to point to its corresponding predicate *)
  let output_branches = EdgeMap.fold (assert_branch soln_var) output_preds base_branches in
  let input_branches = VertexMap.fold (fun innode _ b -> addBranch (node_to_pat innode) etrue b) inputs output_branches in
  let match_exp = amatch node_var (Some TNode) input_branches in
  let lambda = lams [node_var; soln_var] match_exp in
  match e with
  | Some e -> Some (wrap e lambda)
  | None -> Some lambda
