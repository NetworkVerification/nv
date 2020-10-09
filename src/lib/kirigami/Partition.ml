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

(** Helper function to unwrap the predicate. *)
let unwrap_pred maybe_pred = match maybe_pred with
  | Some pred -> pred (* the interface is an efun *)
  (* Make the predicate a function that ignores its argument *)
  | None -> annot TBool (e_val (vbool true))

(* Transform the given solve and return it along with a new expression to assert
 * and new expressions to require. *)
let transform_solve ~(base_check: bool) solve (partition: partitioned_srp) : (solve * exp * exp list) =
  let { aty; var_names; init; trans; merge; interface; _ } : solve = solve in
  let intf_opt : (Edge.t -> exp option) =
    match interface with
    | Some intfe -> (interp_interface intfe)
    | None -> fun (_: Edge.t) -> None
  in
  (* let edge_preds = EdgeMap.fold (fun olde newe m -> match newe with
   *     | Some e -> EdgeMap.add e (intf_opt olde) m
   *     | None -> m) partition.edge_map EdgeMap.empty in *)
  (* Update the partitioned_srp instance with the interface information *)
  let partition' = {
    partition with
    inputs = VertexMap.map (fun input_exps -> List.map (fun input_exp -> { input_exp with pred = (intf_opt input_exp.edge) }) input_exps) partition.inputs;
    outputs = VertexMap.map (fun outputs -> List.map (fun (edge, _) -> (edge, (intf_opt edge))) outputs) partition.outputs;
    (* inputs = VertexMap.mapi (fun innode input_exp -> let new_pred = EdgeMap.find_default None (innode, input_exp.base) edge_preds in
     *                           { input_exp with pred = new_pred }) partition.inputs;
     * outputs = VertexMap.mapi (fun outnode (base, _) -> let new_pred = EdgeMap.find_default None (base, outnode) edge_preds in
     *                            (base, new_pred)) partition.outputs; *)
  } in
  let attr_type = aty |> Option.get in
  let init' = transform_init init merge attr_type partition' in
  let trans' = transform_trans trans attr_type partition' in
  let merge' = transform_merge merge attr_type partition' in
  (* TODO: should we instead create separate let-bindings to refer to init, trans and merge? *)
  let outputs_assert = TransformDecls.outputs_assert trans var_names attr_type partition' in
  let add_require _ inputs l =
    List.fold_left (fun l {var; pred; _} -> match pred with
        | Some p -> (annot TBool (eapp p (annot attr_type (evar var)))) :: l
        | None -> l) l inputs
  in
  let reqs = if base_check then [] else VertexMap.fold add_require partition'.inputs []
  in
  ({
    solve with
    init = init';
    trans = trans';
    merge = merge';
    (* should this be erased, or kept as reference? *)
    interface = None;
  }, outputs_assert, reqs)

let transform_declaration ~(base_check: bool) parted_srp decl =
  let { nodes; edges; _ } : partitioned_srp = parted_srp in
  match decl with
  | DNodes _ -> [DNodes nodes]
  | DEdges _ -> [DEdges edges]
  | DSolve s -> let (solve', assert', reqs) = transform_solve base_check s parted_srp in
    [DSolve solve'; DAssert assert'] @ List.map (fun e -> DRequire e) reqs
  | DPartition _ -> []
  (* If performing the base check, drop existing assertions *)
  | DAssert _ -> if base_check then [] else [decl]
  | _ -> [decl]

(** Create a list of lists of declarations representing a network which has been
 * opened along the edges described by the partition and interface declarations.
 * @return a new list of lists of declarations
*)
let divide_decls (cfg: Cmdline.t) (decls: declarations) ~(base_check: bool) : declarations list =
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
      let tcomp : transcomp = OutputTrans in
      let partitioned_srps = partition_edges node_list edges partf tcomp in
      let create_new_decls (parted_srp : partitioned_srp) : declarations =
        (* TODO: node_map and edge_map describe how to remap each node and edge in the new SRP.
         * To transform more cleanly, we can run a toplevel transformer on the SRP, replacing
         * each edge and node in the map with the new value if it's Some,
         * and removing it if it's None * (where the edge/node is explicitly used).
         * We can then add code to handle adding in the new input and output nodes to the SRP.
         * (the input and output edges are handled by edge_map).
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
        let transformed_decls = List.flatten @@ List.map (transform_declaration ~base_check parted_srp) decls in
        new_symbolics @ transformed_decls
      in
      List.map create_new_decls partitioned_srps
    end
  | None -> [decls]
