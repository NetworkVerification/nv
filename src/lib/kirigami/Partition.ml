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

type transcomp =
  | Decomposed of exp * exp
  | OutputTrans
  | InputTrans

(** Separation of the purposes of the declarations
 ** for a given partitioned SRP. *)
type partitioned_decls = {
  (* new DSymbolic decls *)
  symbolics: declaration list;
  (* new DRequire decls and their corresponding partition ranks *)
  hypotheses: (declaration, int) Map.t;
  (* new DAssert decls for checking hypotheses *)
  guarantees: declaration list;
  (* old DAssert decls for testing network properties *)
  properties: declaration list;
  (* all other network decls, including those defining essential behaviour (init, trans, merge) *)
  network: declaration list;
}

(* Sum type that distinguishes partitioned versus unpartitioned networks,
 * for the purpose of lifting operations over declarations. *)
type declaration_group =
  | Unpartitioned of declarations
  | Partitioned of partitioned_decls


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
let transform_solve ~(transcomp: transcomp) solve (partition: partitioned_srp) : (solve * exp list * (exp, int) Map.t) =
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
  let add_require _ input_exps m =
    List.fold_left (fun m {var; rank; pred; _} -> match pred with
        | Some p -> Map.add (annot TBool (eapp p (annot attr_type (evar var)))) rank m
        | None -> m) m input_exps
  in
  let reqs = VertexMap.fold add_require partition'.inputs Map.empty
  in
  ({
    solve with
    init = init';
    trans = trans';
    merge = merge';
    (* should this be erased, or kept as reference? *)
    interface = None;
  }, outputs_assert, reqs)

(* Return a transformed version of the given declaration, and optionally any new Kirigami constraints
 * that need to be added with it. *)
let transform_declaration ~(transcomp: transcomp) parted_srp decl : (declaration option * declaration list * (declaration, int) Map.t * declaration option) =
  let { nodes; edges; _ } : partitioned_srp = parted_srp in
  match decl with
  | DNodes _ -> (Some (DNodes nodes), [], Map.empty, None)
  | DEdges _ -> (Some (DEdges edges), [], Map.empty, None)
  | DSolve s -> let (solve', assert', reqs) = transform_solve transcomp s parted_srp in
    let req_decls = Map.foldi (fun e r -> Map.add (DRequire e) r) reqs Map.empty in
    (Some (DSolve solve'), List.map (fun e -> DAssert e) assert', req_decls, None)
  | DPartition _ -> (None, [], Map.empty, None)
  | DAssert e -> (None, [], Map.empty, Some (DAssert (transform_assert e parted_srp)))
  | _ -> (Some decl, [], Map.empty, None)

(** Create a list of lists of declarations representing a network which has been
 * opened along the edges described by the partition and interface declarations.
 * @return a new list of lists of declarations
*)
let divide_decls (cfg: Cmdline.t) (decls: declarations) : declaration_group list =
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
      let create_new_decls (parted_srp : partitioned_srp) : declaration_group =
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
        let symbolics = VertexMap.fold add_symbolics parted_srp.inputs [] in
        (* replace relevant old declarations *)
        let transformed_decls = List.map (transform_declaration ~transcomp parted_srp) decls in
        (* divide up the declarations as appropriate *)
        let rec split_decls (net, guar, hyp, prop) l =
          match l with
          | [] -> (net, guar, hyp, prop)
          | (net', guar', hyp', prop') :: t -> split_decls (net' :: net, guar' @ guar, Map.union hyp' hyp, prop' :: prop) t
        in
        let (network, guarantees, hypotheses, properties) = split_decls ([], [], Map.empty, []) transformed_decls in
        Partitioned {
          symbolics;
          hypotheses;
          guarantees;
          properties = List.filter_map (fun a -> a) properties;
          network = List.filter_map (fun a -> a) network;
        }
      in
      List.map create_new_decls partitioned_srps
    end
  | None -> [Unpartitioned decls]

(* TODO: change this not to take a list of map_back functions, but instead to compose the partitioned map_back *)
let lift_decl_transform (f: declarations -> (declarations * Nv_solution.Solution.map_back)) (decls, fs) =
  match decls with
  | Unpartitioned d -> let d', f = f d in (Unpartitioned d', f :: fs)
  | Partitioned { symbolics; hypotheses; guarantees; properties; network; } -> (
      (* FIXME: fiddle with or drop map back functions as necessary *)
      let s, sf = f symbolics in
      let h, hf = Map.foldi (fun hyp rank (m, l) -> let h, hf = f [hyp] in (Map.add (List.hd h) rank m, hf :: l)) hypotheses (Map.empty, []) in
      let g, gf = f guarantees in
      let p, pf = f properties in
      let n, nf = f network in
      (Partitioned { symbolics = s; hypotheses = h; guarantees = g; properties = p; network = n; }, sf :: hf @ gf :: pf :: nf :: fs)
    )
