open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Nv_utils.PrimitiveCollections
open Nv_lang
open Nv_lang.Syntax
open TransformDecls
open Nv_interpreter
open Nv_utils.OCamlUtils
open SrpRemapping

(** Helper function to extract the edge predicate
 *  from the interface expression.
*)
let interp_interface intfe e : exp option =
  let intf_app = Interp.apply empty_env (deconstructFun intfe) (vedge e) in
  (* if intf_app is not an option, or if the value it contains is not a function,
   * fail *)
  match intf_app with
  | {v = VOption o; _} -> begin match o with
      | Some {v = VClosure (_env, func); _ } -> Some (efunc func)
      | Some _ -> failwith "expected a closure, got something else instead!"
      (* infer case *)
      | None -> None
    end
  | _ -> failwith "intf value is not an option; did you type check the input?"

(** Helper function to extract the partition index
 *  from the partition expression.
*)
let interp_partition parte node : int =
  let value = Interp.apply empty_env (deconstructFun parte) (vnode node)
  in (int_of_val value) |> Option.get

(** Interpret the transfer function expression with the given edge and the given expression x. *)
let interp_trans trans edge x : value =
  let edge_exp = e_val (vedge edge) in
  let trans_app = Interp.interp (eapp (eapp trans edge_exp) x) in
  trans_app

(** Return the outgoing transfer function and the incoming transfer function decomposition. *)
let decompose_trans (attr: ty) (trans: exp) (transcomp: transcomp) : (exp * exp) =
  let edge_var = Var.fresh "e" in
  let x_var = Var.fresh "x" in
  let x_lambda = efunc (funcFull x_var (Some attr) (Some attr) (annot attr (evar x_var))) in
  let lambda = efunc (funcFull edge_var (Some TEdge) (Some (TArrow (attr, attr))) x_lambda) in
  let identity = wrap trans lambda in
  match transcomp with
  | OutputTrans -> (trans, identity)
  | InputTrans -> (identity, trans)
  | Decomposed (e1, e2) -> (e1, e2)

(* Transform the given solve and return it along with a new expression to assert
 * and new expressions to require. *)
let transform_solve ~(base_check: bool) ~(transcomp: transcomp) solve (partition: partitioned_srp) : (solve * exp * exp list) =
  let { aty; var_names; init; trans; merge; interface; _ } : solve = solve in
  let intf_opt : (Edge.t -> exp option) =
    match interface with
    | Some intfe -> (interp_interface intfe)
    | None -> fun (_: Edge.t) -> None
  in
  (* Update the partitioned_srp instance with the interface information *)
  let partition' = {
    partition with
    inputs = VertexMap.map (fun input_exps -> List.map (fun input_exp -> { input_exp with pred = (intf_opt input_exp.edge) }) input_exps) partition.inputs;
    outputs = VertexMap.map (fun outputs -> List.map (fun (edge, _) -> (edge, (intf_opt edge))) outputs) partition.outputs;
  } in
  let attr_type = aty |> Option.get in
  let (outtrans, intrans) = decompose_trans attr_type trans transcomp in
  let init' = transform_init init intrans merge attr_type partition' in
  let trans' = transform_trans trans attr_type partition' in
  let merge' = transform_merge merge attr_type partition' in
  (* TODO: should we instead create separate let-bindings to refer to init, trans and merge? *)
  let outputs_assert = TransformDecls.outputs_assert outtrans var_names attr_type partition' in
  let add_require _ inputs l =
    List.fold_left (fun l {var; rank; pred; _} -> match pred with
        (* if we are performing the initial check, skip any predicates with rank higher than this partition *)
        | Some p -> if base_check && partition.rank < rank then l else (annot TBool (eapp p (annot attr_type (evar var)))) :: l
        | None -> l) l inputs
  in
  let reqs = VertexMap.fold add_require partition'.inputs []
  in
  ({
    solve with
    init = init';
    trans = trans';
    merge = merge';
    (* should this be erased, or kept as reference? *)
    interface = None;
  }, outputs_assert, reqs)

let transform_declaration ~(base_check: bool) ~(transcomp: transcomp) parted_srp _constraint_set decl =
  let { nodes; edges; _ } : partitioned_srp = parted_srp in
  match decl with
  | DNodes _ -> [DNodes nodes]
  | DEdges _ -> [DEdges edges]
  | DSolve s -> let (solve', assert', reqs) = transform_solve base_check transcomp s parted_srp in
    [DSolve solve'; DAssert assert'] @ List.map (fun e -> DRequire e) reqs
  | DPartition _ -> []
  (* If performing the base check, drop existing assertions *)
  | DAssert e -> if base_check then [] else [DAssert (transform_assert e parted_srp)]
  | _ -> [decl]

(** Create a list of lists of declarations representing a network which has been
 * opened along the edges described by the partition and interface declarations.
 * @return a new list of lists of declarations
*)
let divide_decls (cfg: Cmdline.t) (decls: declarations) ~(base_check: bool) : (declarations * exp Set.t) list =
  let partition = get_partition decls in
  match partition with
  | Some parte -> begin
      let attr_type = get_attr_type decls |> Option.get in
      (* get the parameters for partition_edges *)
      let nodes = get_nodes decls |> Option.get in
      let node_list = List.range 0 `To (nodes - 1) in
      let edges = get_edges decls |> Option.get in
      (* interpret partition function *)
      let partf : (Vertex.t -> int) = interp_partition parte in
      (* TODO: change this to a cmdline parameter *)
      let transcomp : transcomp = OutputTrans in
      let partitioned_srps = partition_edges node_list edges partf in
      let create_new_decls (parted_srp : partitioned_srp) : (declarations * exp Set.t) =
        (* TODO: node_map and edge_map describe how to remap each node and edge in the new SRP.
         * To transform more cleanly, we can run a toplevel transformer on the SRP, replacing
         * each edge and node in the map with the new value if it's Some,
         * and removing it if it's None (where the edge/node is explicitly used).
        *)
        (* Print mapping from old nodes to new nodes *)
        if cfg.print_remap then
          let remap_node v = match v with
            | Some v -> string_of_int v
            | None -> "cut"
          in
          print_endline @@ VertexMap.to_string remap_node parted_srp.node_map
        else ();
        let add_symbolics _ inputs l =
          List.fold_left (fun l {var; _} -> DSymbolic (var, Ty attr_type) :: l) l inputs
        in
        let new_symbolics = VertexMap.fold add_symbolics parted_srp.inputs [] in
        (* replace relevant old declarations *)
        let constraint_set = Set.empty in
        let transformed_decls = List.flatten @@ List.map (transform_declaration ~base_check ~transcomp parted_srp constraint_set) decls in
        (new_symbolics @ transformed_decls, constraint_set)
      in
      List.map create_new_decls partitioned_srps
    end
  | None -> [(decls, Set.empty)]
