open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax
open Nv_interpreter

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

(* Return a Let declaration of a function that maps from old nodes to new nodes. *)
let node_map_decl fnname (m: Vertex.t option VertexMap.t) =
  let node_var = Var.create "n" in
  let branches = match_of_node_map m emptyBranch in
  DLet
    (
      Var.create fnname,
      None,
      efun
        {arg = node_var; argty = None; resty = None;
         body =
           ematch (evar node_var) branches
        }
    )

(** Add match branches using the given map of old edges to new edges. *)
let match_of_edge_map (m: Edge.t option EdgeMap.t) b =
  let add_edge_branch old_edge new_edge branches =
    match new_edge with
    | Some e -> addBranch (edge_to_pat e) (edge_to_exp old_edge) branches
    | None -> branches
  in
  EdgeMap.fold add_edge_branch m b

(* Return a Let declaration of a function that maps from old edges to new edges. *)
let edge_map_decl fnname (m: Edge.t option EdgeMap.t) =
  let edge_var = Var.create "e" in
  let branches = match_of_edge_map m emptyBranch in
  DLet
    (
      Var.create fnname,
      None,
      efun
        {arg = edge_var; argty = None; resty = None;
         body =
           ematch (evar edge_var) branches
        }
    )

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
  (* Simplify the old expression to a value *)
  let interp_old old exp =
    InterpPartial.interp_partial_opt (eapp old exp)
  in
  let base_branches = mapBranches (fun (pat,exp) -> (pat, interp_old old exp)) base_map_match in
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
  let orig_trans edge = (apps e [edge; (evar x_var)]) in
  (* Simplify the old expression to an expression just over the second variable *)
  let interp_trans edge =
    InterpPartial.interp_partial_opt (orig_trans edge)
  in
  (* function to remap edge_map mappings to the correct trans expressions *)
  let remap_branch (pat, exp) = match pat with
    | (PEdge (PNode u, PNode v)) -> begin
        (* handle if the nodes are base~base, input~base, or base~output *)
        let new_exp = match VertexMap.Exceptionless.find v outputs with
          | Some u' -> if (u = u') then (interp_trans exp)
          (* call the original exp using the old edge *)
            else failwith "outputs stored edge did not match edge in edge_map"
          | None -> begin
              (* not a base~output edge, check input~base case *)
              match VertexMap.Exceptionless.find u inputs with
              | Some v' -> if (v = v') then (evar x_var) else
                  failwith "inputs stored edge did not match edge in edge_map"
              | None -> (interp_trans exp) (* must be a base~base edge *)
            end
        in
        (pat, new_exp)
      end
    | _ -> failwith "bad match pattern"
  in
  let edge_map_match = match_of_edge_map edge_map emptyBranch in
  let branches = mapBranches remap_branch edge_map_match in
  wrap e (lams [edge_var; x_var] (amatch edge_var (Some TEdge) branches))

let in_merge_branch (n: Vertex.t) (_: Vertex.t) (b: branches) : branches =
  let a1 = Var.fresh "a1" in
  let a2 = Var.fresh "a2" in
  let node_pat = node_to_pat n in
  (* create a function that takes 2 attributes and returns the first one *)
  (* FIXME: this is a *brittle and dangerous solution*, since it relies on an
   * implementation detail to ignore the fact that we expect merge to be
   * commutative *)
  let merge_exp = (lams [a1; a2] (evar a1)) in
  addBranch node_pat merge_exp b

let out_merge_branch (n: Vertex.t) (_: Vertex.t) (b: branches) : branches =
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
  let { outputs; inputs } : SrpRemapping.interface = intf in
  (* let default_branch = addBranch PWild e emptyBranch in *)
  let map_match = match_of_node_map node_map emptyBranch in
  (* Simplify the old expression to a smaller expression *)
  let interp_old old exp =
    InterpPartial.interp_partial_opt (eapp old exp)
  in
  let base_branches = mapBranches (fun (pat, exp) -> (pat, interp_old e exp)) map_match in
  (* FIXME: bad merge impl for inputs; left as-is for now since it's not actually called,
   * just present to stop there from being complaints about missing branches in the match *)
  let input_branches = VertexMap.fold in_merge_branch inputs base_branches in
  let output_branches = VertexMap.fold out_merge_branch outputs input_branches in
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
  : Syntax.exp =
  let { inputs; _ } : SrpRemapping.interface = intf in
  let node_var = Var.fresh "node" in
  let soln_var = Var.fresh "x" in
  let etrue = e_val (vbool true) in
  (* If the old expression was Some, apply the assert with the given variables;
   * if it was None, simply create an expression evaluating to true *)
  let apply_assert node soln = match e with
    (* Apply the old assert and simplify if possible *)
    | Some e -> InterpPartial.interp_partial (apps e [node; soln])
    | None -> etrue
  in
  (* Map the new base nodes to the old ones using the map_match *)
  let map_match = match_of_node_map node_map emptyBranch in
  let base_branches = mapBranches (fun (pat, exp) -> (pat, apply_assert exp (evar soln_var))) map_match in
  (* re-map every output to point to its corresponding predicate *)
  let output_branches = EdgeMap.fold (assert_branch soln_var) output_preds base_branches in
  let input_branches = VertexMap.fold (fun innode _ b -> addBranch (node_to_pat innode) etrue b) inputs output_branches in
  let match_exp = amatch node_var (Some TNode) input_branches in
  let lambda = lams [node_var; soln_var] match_exp in
  match e with
  | Some e -> (wrap e lambda)
  | None -> lambda
