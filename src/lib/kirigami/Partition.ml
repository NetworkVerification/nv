open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph
open Nv_utils.PrimitiveCollections
open Nv_lang.Syntax
open TransformDecls
open Nv_interpreter
open Nv_utils.OCamlUtils

let is_cross_partition (f: Vertex.t -> 'a) edge =
  (f (fst edge)) <> (f (snd edge))

(* It is possible that a better implementation involves building a new graph using the interface set,
 * as indexing newly-added nodes could break on AdjGraph implementation change
*)

(** Representation of a cut edge with an associated hypothesis and a predicate on that hypothesis *)
type cut_edge =
  { u: Vertex.t;
    v: Vertex.t;
    h: var;
    p: exp;
  }

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

(* Generate a map of edges to annotations from the given partition and interface expressions
 * and a list of edges.
 * If the interface is absent, use None for each value.
 * @return a map from edges in the original SRP to associated values
*)
let map_edges_to_interface (partition: exp option) (interface: exp option) (edges: edge list) : exp option EdgeMap.t =
  match partition with
  | Some parte -> begin
      let get_edge_hyp map e =
        (* Add each cross-partition edge to the interface *)
        if (is_cross_partition (interp_partition parte) e) then
          let intf_pred = match interface with
            | Some intfe -> interp_interface intfe e
            | None -> None
          in
          EdgeMap.add e intf_pred map
        else
          map
      in
      List.fold_left get_edge_hyp EdgeMap.empty edges
    end
  | None -> EdgeMap.empty

(** Helper function to unwrap the predicate. *)
let unwrap_pred maybe_pred = match maybe_pred with
  | Some pred -> pred (* the interface is an efun *)
  | None -> e_val (vbool true)

(** Create a symbolic variable for each cut edge.
 *  This function maps each edge's optional predicate
 *  into a pair: a hypothesis variable and a predicate we can
 *  apply to that hypothesis variable.
 *  @return a map from edges to hypothesis and predicate information *)
let create_hyp_vars (interface: exp option EdgeMap.t) : (var * exp) EdgeMap.t =
  let create_hyp_pred edge maybe_pred =
    (* generate the var *)
    let name = Printf.sprintf "hyp_%s" (Edge.to_string edge) in
    (Var.fresh name, unwrap_pred maybe_pred)
  in
  EdgeMap.mapi create_hyp_pred interface

(** Create a new map from the given map of cut edges to hypothesis-predicate pairs,
 *  where each key is an input~base edge, and each value is an expression using the hypothesis.
 *  This is then used to add the input cases to the init function.
*)
let get_input_exps ({ broken_ins; _}: OpenAdjGraph.interfaces_alt) (edge_hyps: (var * exp) EdgeMap.t) : (exp EdgeMap.t) =
  (* create an edgemap of input~base keys to hypothesis expression values *)
  let add_edge_to_hyp (u, v) inn m =
    let (var, _) = EdgeMap.find (u,v) edge_hyps in
    EdgeMap.add (inn,v) (evar var) m
  in
  EdgeMap.fold add_edge_to_hyp broken_ins EdgeMap.empty

(* filter all predicate edges out that do not appear in the given vertex->vertex map *)
let filter_preds vmap preds =
  (* match on both binding arrangements:
   * since outputs go output~base but preds goes base~output,
   * there's no risk of mismatching, since outputs and input all
   * have only one neighbor
  *)
  let find_pred_in_vmap (u, v) _ =
    let is_pred_in_vmap u' v' = (u' = u && v' = v ) || (u' = v && v' = u) in
    VertexMap.exists is_pred_in_vmap vmap
  in
  EdgeMap.filter find_pred_in_vmap preds

let transform_declaration parted_srp attr_type decl =
  let { nodes; edges; _ } : SrpRemapping.partitioned_srp = parted_srp in
  match decl with
  | DNodes _ -> Some (DNodes nodes)
  | DEdges _ -> Some (DEdges edges)
  | DInit init -> begin
      (* let input_exps = EdgeMap.map (fun (v, _) -> (evar v)) input_hyps in *)
      Some (DInit (transform_init init attr_type parted_srp))
    end
  | DTrans trans -> Some (DTrans (transform_trans trans attr_type parted_srp))
  (* FIXME: merge is screwy; currently an output node on the destination won't update since it
    * gets initialized with the destination's value, which is already the best *)
  | DMerge merge -> Some (DMerge (transform_merge merge attr_type parted_srp))
  | DAssert assertion -> begin
      (* let output_preds = filter_preds intf.outputs preds in *)
      Some (DAssert (transform_assert (Some assertion) attr_type parted_srp))
    end
  | DPartition _ -> None
  | DInterface _ -> None
  | _ -> Some decl

(** Create a list of lists of declarations representing a network which has been
 * opened along the edges described by the partition and interface declarations.
 * @return a new list of lists of declarations
*)
let divide_decls (decls: declarations) : declarations list =
  let partition = get_partition decls in
  match partition with
  | Some parte -> begin
      (* Give names to remap functions *)
      (* let node_remap_fn = "remapNode" in
       * let edge_remap_fn = "remapEdge" in *)
      let attr_type = get_attr_type decls |> Option.get in
      (* get the parameters for partition_edges *)
      let interface = get_interface decls in
      let nodes = get_nodes decls |> Option.get in
      let node_list = List.range 0 `To (nodes - 1) in
      let edges = get_edges decls |> Option.get in
      (* interpret partition and interface functions *)
      let partf : (Vertex.t -> int) = interp_partition parte in
      let intf_opt : (Edge.t -> exp option) =
        match interface with
        | Some intfe -> (interp_interface intfe)
        | None -> fun (_: Edge.t) -> None
      in
      let interfacef = unwrap_pred % intf_opt in
      let partitioned_srps = SrpRemapping.partition_edges node_list edges partf interfacef in
      let create_new_decls (parted_srp : SrpRemapping.partitioned_srp) : declarations =
        (* TODO: node_map and edge_map describe how to remap each node and edge in the new SRP.
         * To transform more cleanly, we can run a toplevel transformer on the SRP, replacing
         * each edge and node in the map with the new value if it's Some,
         * and removing it if it's None * (where the edge/node is explicitly used).
         * We can then add code to handle adding in the new input and output nodes to the SRP.
         * (the input and output edges are handled by edge_map).
        *)
        let add_symbolic _ ({var; _} : SrpRemapping.input_exp) l =
          DSymbolic (var, Ty attr_type) :: l
        in
        let new_symbolics = VertexMap.fold add_symbolic parted_srp.inputs [] in
        let add_require _ ({var; pred; _} : SrpRemapping.input_exp) l =
          DRequire (eapp pred (evar var)) :: l
        in
        let new_requires = VertexMap.fold add_require parted_srp.inputs [] in
        (* replace relevant old decls *)
        let new_decls = List.filter_map (transform_declaration parted_srp attr_type) decls in
        (* add the assertion in at the end if there wasn't an assert in the original decls *)
        let add_assert = match get_assert new_decls with
          | Some _ -> []
          | None -> [DAssert (transform_assert None attr_type parted_srp)]
        in
        (* also add requires at the end so they can use any bindings earlier in the file *)
        new_symbolics @ new_decls @ new_requires @ add_assert
      in
      List.map create_new_decls partitioned_srps
    end
  | None -> [decls]
