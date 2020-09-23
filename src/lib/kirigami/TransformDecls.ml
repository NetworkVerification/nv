open Batteries
open Nv_lang
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Syntax
open Nv_interpreter

let node_to_exp n = e_val (vnode n)

let edge_to_exp e = e_val (vedge e)

let node_to_pat node = exp_to_pattern (node_to_exp node)

let edge_to_pat edge = exp_to_pattern (edge_to_exp edge)

(* Create an annotated match statement *)
let amatch v t b = annot t (ematch (aexp (evar v, Some t, Span.default)) b)

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
      Some (TArrow (TNode, TNode)),
      efun
        {arg = node_var; argty = Some TNode; resty = Some TNode;
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
      Some (TArrow (TEdge, TEdge)),
      efun
        {arg = edge_var; argty = Some TEdge; resty = Some TEdge;
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
let transform_init (old: exp) (merge: exp) (ty: ty) (parted_srp: SrpRemapping.partitioned_srp) : Syntax.exp =
  let {node_map; inputs; _} : SrpRemapping.partitioned_srp = parted_srp in
  let interp arg = InterpPartial.interp_partial_fun old [arg] in
  (* FIXME: perform an inlined sequence of merge operations, one for each input *)
  let node_var = Var.fresh "node" in
  let add_input_branch u input_exp =
    (* if the edge is present in the interface set, then use the specified expression;
     * this should be true only for the input edges since input_exps lists input~base edges *)
    let { var; _ } : SrpRemapping.input_exp = input_exp in
    let exp = annot ty (evar var) in
    addBranch (node_to_pat u) exp
  in
  let add_output_branch u (v, _) =
    (* the output applies the old init with the old base node *)
    let exp = interp (vnode v) in
    addBranch (node_to_pat u) exp
  in
  let base_map_match = match_of_node_map node_map emptyBranch in
  let base_branches = mapBranches (fun (pat,exp) -> (pat, interp (Syntax.to_value exp))) base_map_match in
  let branches = VertexMap.fold add_input_branch inputs base_branches in
  (* let output_branches = VertexMap.fold add_output_branch outputs input_branches in *)
  (* the returned expression should be a function that takes a node as input with the following body:
   * a match with node as the exp and output_branches as the branches *)
  wrap old (efunc (funcFull node_var (Some TNode) (Some ty) (amatch node_var TNode branches)))

(* Pass in the original trans Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * two parameters of types tedge and attribute
*)
(* let transform_trans (e: exp) (attr: ty) (parted_srp: SrpRemapping.partitioned_srp) : Syntax.exp =
 *   let { inputs; outputs; edge_map; trans } : SrpRemapping.partitioned_srp = parted_srp in
 *   (\* new function argument *\)
 *   let edge_var = Var.fresh "edge" in
 *   let x_var = Var.fresh "x" in
 *   (\* Simplify the old expression to an expression just over the second variable *\)
 *   let interp_trans edge =
 *     InterpPartial.interp_partial_opt (annot attr (apps e [edge; annot attr (evar x_var)]))
 *   in
 *   (\* function to remap edge_map mappings to the correct trans expressions *\)
 *   let remap_branch (pat, edge) = match pat with
 *     | (PEdge (PNode u, PNode v)) -> begin
 *         (\* the trans field of parted_srp tells us how to decompose the transfer function *\)
 *         let (out_exp, in_exp) = match trans with
 *           | SrpRemapping.OutputTrans -> (interp_trans edge, annot attr (evar x_var))
 *           | SrpRemapping.InputTrans -> (annot attr (evar x_var), interp_trans edge)
 *           | SrpRemapping.Decomposed (e1, e2) -> (e1, e2)
 *         in
 *         (\* handle if the nodes are base~base, input~base, or base~output *\)
 *         let new_exp = match VertexMap.Exceptionless.find v outputs with
 *           | Some (u', _) -> if (u = u') then out_exp
 *             else failwith "outputs stored edge did not match edge in edge_map"
 *           | None -> begin
 *               (\* not a base~output edge, check input~base case *\)
 *               match VertexMap.Exceptionless.find u inputs with
 *               | Some {base; _ } -> if (v = base) then in_exp else
 *                   failwith "inputs stored edge did not match edge in edge_map"
 *               | None -> (interp_trans edge) (\* must be a base~base edge *\)
 *             end
 *         in
 *         (pat, new_exp)
 *       end
 *     | _ -> failwith "bad match pattern"
 *   in
 *   let edge_map_match = match_of_edge_map edge_map emptyBranch in
 *   let branches = mapBranches remap_branch edge_map_match in
 *   let x_lambda = efunc (funcFull x_var (Some attr) (Some attr) (annot attr (amatch edge_var TEdge branches))) in
 *   let lambda = efunc (funcFull edge_var (Some TEdge) (Some (TArrow (attr, attr))) x_lambda) in
 *   wrap e lambda *)

(* let in_merge_branch (ty: ty) (n: Vertex.t) (_: SrpRemapping.input_exp) (b: branches) : branches =
 *   let a1 = Var.fresh "a1" in
 *   let a2 = Var.fresh "a2" in
 *   let node_pat = node_to_pat n in
 *   (\* create a function that takes 2 attributes and returns the first one *\)
 *   (\* FIXME: this is a *brittle and dangerous solution*, since it relies on an
 *    * implementation detail to ignore the fact that we expect merge to be
 *    * commutative *\)
 *   let a2_lambda = efunc (funcFull a2 (Some ty) (Some ty) (annot ty (evar a1))) in
 *   let a1_lambda = efunc (funcFull a1 (Some ty) (Some (TArrow (ty, ty))) a2_lambda) in
 *   addBranch node_pat a1_lambda b *)

(* let out_merge_branch (ty: ty) (n: Vertex.t) (_: (Vertex.t * exp option)) (b: branches) : branches =
 *   let a1 = Var.fresh "a1" in
 *   let a2 = Var.fresh "a2" in
 *   let node_pat = node_to_pat n in
 *   (\* create a function that takes 2 attributes and returns the second one *\)
 *   (\* FIXME: this is a *brittle and dangerous solution*, since it relies on an
 *    * implementation detail to ignore the fact that we expect merge to be
 *    * commutative *\)
 *   let a2_lambda = efunc (funcFull a2 (Some ty) (Some ty) (annot ty (evar a2))) in
 *   let a1_lambda = efunc (funcFull a1 (Some ty) (Some (TArrow (ty, ty))) a2_lambda) in
 *   addBranch node_pat a1_lambda b *)

(* let transform_merge (e: exp) (ty: ty) (parted_srp: SrpRemapping.partitioned_srp) : exp =
 *   let { node_map; outputs; inputs } : SrpRemapping.partitioned_srp = parted_srp in
 *   (\* the internal type after matching on the node *\)
 *   let inner_ty = TArrow (ty, TArrow (ty, ty)) in
 *   let node_var = Var.fresh "node" in
 *   (\* let default_branch = addBranch PWild e emptyBranch in *\)
 *   let map_match = match_of_node_map node_map emptyBranch in
 *   (\* Simplify the old expression to a smaller expression *\)
 *   let interp_old old exp =
 *     InterpPartial.interp_partial_opt (annot inner_ty (eapp old exp))
 *   in
 *   let base_branches = mapBranches (fun (pat, exp) -> (pat, interp_old e exp)) map_match in
 *   (\* FIXME: bad merge impl for inputs; left as-is for now since it's not actually called,
 *    * just present to stop there from being complaints about missing branches in the match *\)
 *   let input_branches = VertexMap.fold (in_merge_branch ty) inputs base_branches in
 *   let output_branches = VertexMap.fold (out_merge_branch ty) outputs input_branches in
 *   wrap e (efunc (funcFull node_var (Some TNode) (Some inner_ty) (amatch node_var TNode output_branches))) *)

(* Apply the predicate test on the solution for node n *)
let assert_branch (x: var) (attr: ty) (outn: Vertex.t)  (_, pred) (b: branches) : branches =
  let node_pat = node_to_pat outn in
  match pred with
  | Some p -> addBranch node_pat (annot TBool (eapp p (annot attr (evar x)))) b
  | None -> addBranch node_pat (annot TBool (e_val (vbool true))) b

(* Check that the solution's value at a particular output vertex satisfies the predicate. *)
let add_output_pred (trans: exp) (attr: ty) (sol: exp) (n: Vertex.t) (edge, pred) acc =
  let sol_x = annot attr (eop MGet [sol; (annot TNode (node_to_exp n))]) in
  let trans_curried = annot (TArrow (attr, attr)) (eapp trans (annot TEdge (edge_to_exp edge))) in
  match pred with
  | Some p -> (annot TBool (eapp p (annot attr (eapp trans_curried sol_x)))) :: acc
  | None -> acc

(* Check each output's solution in the sol variable. *)
let outputs_assert (trans: exp) (sol: exp) (attr: ty) (parted_srp: SrpRemapping.partitioned_srp) : exp =
  let { outputs; _ } : SrpRemapping.partitioned_srp = parted_srp in
  (* re-map every output to point to its corresponding predicate *)
  let output_preds = VertexMap.fold (add_output_pred trans attr sol) outputs [] in
  (* Return a conjunction of the output assertions *)
  if (List.length output_preds) > 1 then
    annot TBool (eop And output_preds)
  else
    annot TBool (List.hd output_preds)