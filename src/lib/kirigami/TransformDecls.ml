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
let match_of_node_map (m: Vertex.t option VertexMap.t) (f: Vertex.t -> Vertex.t -> exp) b =
  let add_node_branch old_node new_node branches =
    match new_node with
    | Some n -> addBranch (node_to_pat n) (f n old_node) branches
    | None -> branches
    (* if there is no new node, just map the old node to itself *)
    (* addBranch (node_to_pat old_node) (node_to_exp old_node) branches *)
  in
  VertexMap.fold add_node_branch m b

(* Return a Let declaration of a function that maps from old nodes to new nodes. *)
let node_map_decl fnname (m: Vertex.t option VertexMap.t) =
  let node_var = Var.create "n" in
  let branches = match_of_node_map m (fun _ -> node_to_exp) emptyBranch in
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
*)
let transform_init (init: exp) (trans: exp) (merge: exp) (ty: ty) (parted_srp: SrpRemapping.partitioned_srp) : Syntax.exp =
  let {node_map; inputs; _} : SrpRemapping.partitioned_srp = parted_srp in
  let node_var = Var.fresh "node" in
  (* function we recursively call to build up the new base node init *)
  let merge_input node node_exp input_exp =
    let { var; edge; _ } : SrpRemapping.input_exp = input_exp in
    let input_exp = annot ty (evar var) in
    (* perform the input transfer on the input exp *)
    let trans_curried = annot (TArrow (ty, ty)) (eapp trans (annot TEdge (edge_to_exp edge))) in
    let trans_input_exp = InterpPartial.interp_partial_opt (annot ty (eapp trans_curried input_exp)) in
    (* perform the merge function, using the given node and its current value with the input variable *)
    let curried_node = annot (TArrow ((TArrow (ty, ty)), ty)) (InterpPartial.interp_partial_fun merge [node]) in
    let curried_node_exp = annot (TArrow (ty, ty)) (eapp curried_node node_exp) in
    wrap node_exp (eapp curried_node_exp trans_input_exp)
  in
  (* we use both node names here since the inputs are organized acc. to new node name, while the old node name
   * is needed to interpret the old function *)
  let interp node = InterpPartial.interp_partial_fun init [(vnode node)] in
  let map_nodes new_node old_node = match VertexMap.Exceptionless.find new_node inputs with
    | Some input_nodes -> List.fold_left (fun e input -> merge_input (vnode old_node) e input) (interp old_node) input_nodes
    | None -> interp old_node
  in
  let branches = match_of_node_map node_map map_nodes emptyBranch in
  (* the returned expression should be a function that takes a node as input with the following body:
   * a match with node as the exp and output_branches as the branches *)
  wrap init (efunc (funcFull node_var (Some TNode) (Some ty) (amatch node_var TNode branches)))

(* Pass in the original trans Syntax.exp and update it to perform
 * distinct actions for the inputs and outputs of the OpenAdjGraph.
 * The expression that is passed in should be a function which has
 * two parameters of types tedge and attribute
*)
let transform_trans (e: exp) (attr: ty) (parted_srp: SrpRemapping.partitioned_srp) : Syntax.exp =
  let { edge_map; _ } : SrpRemapping.partitioned_srp = parted_srp in
  (* new function argument *)
  let edge_var = Var.fresh "edge" in
  let x_var = Var.fresh "x" in
  (* Simplify the old expression to an expression just over the second variable *)
  let interp_trans edge =
    InterpPartial.interp_partial_opt (annot attr (apps e [edge; annot attr (evar x_var)]))
  in
  let edge_map_match = match_of_edge_map edge_map emptyBranch in
  let branches = mapBranches (fun (pat, edge) -> (pat, interp_trans edge)) edge_map_match in
  let x_lambda = efunc (funcFull x_var (Some attr) (Some attr) (annot attr (amatch edge_var TEdge branches))) in
  let lambda = efunc (funcFull edge_var (Some TEdge) (Some (TArrow (attr, attr))) x_lambda) in
  wrap e lambda

let transform_merge (e: exp) (ty: ty) (parted_srp: SrpRemapping.partitioned_srp) : exp =
  let { node_map; _ } : SrpRemapping.partitioned_srp = parted_srp in
  (* the internal type after matching on the node *)
  let inner_ty = TArrow (ty, TArrow (ty, ty)) in
  let node_var = Var.fresh "node" in
  (* Simplify the old expression to a smaller expression *)
  let interp_old old exp =
    InterpPartial.interp_partial_opt (annot inner_ty (eapp old exp))
  in
  let branches = match_of_node_map node_map (fun _ old -> interp_old e (node_to_exp old)) emptyBranch in
  wrap e (efunc (funcFull node_var (Some TNode) (Some inner_ty) (amatch node_var TNode branches)))

(* Check that the solution's value at a particular output vertex satisfies the predicate. *)
let add_output_pred (trans: exp) (attr: ty) (sol: exp) (n: Vertex.t) (edge, pred) acc =
  let sol_x = annot attr (eop MGet [sol; (annot TNode (node_to_exp n))]) in
  (* partially interpret the transfer function *)
  let trans_app = (eapp trans (annot TEdge (edge_to_exp edge))) in
  let trans_curried = InterpPartial.interp_partial_opt (annot (TArrow (attr, attr)) trans_app) in
  match pred with
  | Some p -> (annot TBool (eapp p (annot attr (eapp trans_curried sol_x)))) :: acc
  | None -> acc

(* Check each output's solution in the sol variable. *)
let outputs_assert (trans: exp) (sol: exp) (attr: ty) (parted_srp: SrpRemapping.partitioned_srp) : exp =
  let { outputs; _ } : SrpRemapping.partitioned_srp = parted_srp in
  (* re-map every output to point to its corresponding predicate *)
  let add_preds n outputs acc = List.fold_left (fun acc output -> add_output_pred trans attr sol n output acc) acc outputs in
  let output_preds = VertexMap.fold add_preds outputs [] in
  (* Return a conjunction of the output assertions *)
  if (List.length output_preds) > 1 then
    annot TBool (eop And output_preds)
  else
    annot TBool (List.hd output_preds)

let transform_assert (e: exp) (_parted_srp: SrpRemapping.partitioned_srp) : exp =
  (* TODO: drop expressions or simplify them to true if they reference nodes we don't have access to *)
  (* NOTE: this may not even be occurring in the assert itself, but in another part of the program;
   * although maybe that's fine if it's already inlined *)
  (* TODO: can use the SrpRemapping transformer to handle this! *)
  e
