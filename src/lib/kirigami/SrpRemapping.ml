open Batteries
open Nv_datastructures.AdjGraph
open Nv_lang
open Nv_lang.Syntax
open Nv_datastructures
open Nv_utils.OCamlUtils

(* A record for managing the input node information *)
type input_exp =
  { (* the associated original edge *)
    edge : E.t
  ; (* the variables associated with the input node *)
    var_names : Var.t list
  ; (* the partition rank of the associated output *)
    rank : int
  ; (* the associated predicate expressions: functions over attributes *)
    preds : exp list
  }

(* the symbolic variable will have the form hyp_delim ^ hyp_prefix ^ [edge] ^ hyp_delim *)
let hyp_prefix = "assume_"
let hyp_delim = '$'

let edge_to_hyp (u, v) =
  Var.fresh
    (Printf.sprintf
       "%c%s%s~%s%c"
       hyp_delim
       hyp_prefix
       (Vertex.to_string u)
       (Vertex.to_string v)
       hyp_delim)
;;

let is_hyp_var e v = String.exists (Var.name v) (Var.name (edge_to_hyp e))

let var_to_edge (v : Var.t) =
  let base =
    try Some (String.cut_on_char hyp_delim 1 (Var.name v)) with
    | Not_found -> None
  in
  let string_to_edge s =
    Tuple2.map int_of_string int_of_string (String.split s ~by:"~")
  in
  Option.map (fun s -> string_to_edge (String.tail s (String.length hyp_prefix))) base
;;

(** A type for transforming the declarations over the old SRP
 ** to declarations for the new partitioned SRP.
 ** The nodes and edges maps help us to remap nodes and edges.
 ** If an old node or edge is not a value in the map,
 ** then we know it has been removed and we can drop it from
 ** the SRP.
 ** The predicates help us keep track of the `interface` predicates
 ** associated with a given new edge, since both inputs and outputs
 ** have associated predicates (required on the hypotheses and
 ** asserted on the output solutions, respectively).
 **)
type partitioned_srp =
  { (* the rank of the partitioned srp *)
    rank : int
  ; (* the nodes in the network *)
    nodes : Vertex.t list
  ; (* the edges in the network *)
    edges : Edge.t list
  ; (* list of bools corresponding to nodes in the monolithic network in reverse order,
     * where [List.nth i (List.rev cut_mask) = true] iff [List.mem i nodes]
     *)
    cut_mask : bool list
  ; (* Maps from base nodes to their inputs and outputs *)
    (* the predicate applies to the input node as a `require`
     * on the hypothesis symbolic variable, and to the
     * output node as an `assert` on the solution
     *)
    inputs : input_exp list VertexMap.t
  ; outputs : (Edge.t * exp list) list VertexMap.t
  }

(* Return the old edges which crossed into this partitioned SRP. *)
let get_cross_edges parted_srp =
  let add_input_edges _ ies l = List.map (fun ie -> ie.edge) ies @ l in
  VertexMap.fold add_input_edges parted_srp.inputs []
;;

let string_of_input_exp { var_names; rank; edge; preds } =
  Printf.sprintf
    "vars %s (%d)\n%s: preds %s"
    (list_to_string Var.name var_names)
    rank
    (Edge.to_string edge)
    (list_to_string Printing.exp_to_string preds)
;;

let string_of_partitioned_srp p =
  let output_to_string (e, p) =
    Printf.sprintf
      "%s: preds %s"
      (Edge.to_string e)
      (list_to_string Printing.exp_to_string p)
  in
  let inputs = VertexMap.to_string (list_to_string string_of_input_exp) p.inputs in
  let outputs = VertexMap.to_string (list_to_string output_to_string) p.outputs in
  Printf.sprintf
    "Partition %d:\nnodes: %s\nedges: %s\ninputs:\n%s\noutputs:\n%s\n"
    p.rank
    (list_to_string Vertex.to_string p.nodes)
    (list_to_string Edge.to_string p.edges)
    inputs
    outputs
;;

let map_predicates f partitioned_srp =
  let inf ie = { ie with preds = f ie.edge ie.preds } in
  let outf (e, ps) = e, f e ps in
  { partitioned_srp with
    inputs = VertexMap.map (fun is -> List.map inf is) partitioned_srp.inputs
  ; outputs = VertexMap.map (fun os -> List.map outf os) partitioned_srp.outputs
  }
;;

(** Map each vertex in the list of vertices to a partition number.
 *  Return the map and the number of partitions.
*)
let map_vertices_to_parts graph (partf : Vertex.t -> int) : int VertexMap.t * int =
  let add_vertex v (m, a) =
    let vnum = partf v in
    (* add the vertex and its partition mapping,
     * and increase the map number if it is the new largest mapping *)
    VertexMap.add v vnum m, max vnum a
  in
  AdjGraph.fold_vertex add_vertex graph (VertexMap.empty, 0)
;;

(* Type for distinguishing cross edges from internal edges *)
type srp_edge =
  (* Internal i: represents an edge internal to an SRP [i] *)
  | Internal of int
  (* Cross i j: represents an edge that crosses from SRP [i] to SRP [j] *)
  | Cross of int * int

(** Return the remapped form of the given edge along with the SRPs it belongs to.
*)
let get_srp_edge edge (node_srps : int VertexMap.t) : srp_edge =
  let u, v = edge in
  (* For the given old vertex, find the associated new vertex *)
  let usrp = VertexMap.find u node_srps in
  let vsrp = VertexMap.find v node_srps in
  if usrp != vsrp then (* cross-partition case *)
                    Cross (usrp, vsrp) else Internal usrp
;;

(** Add the edge to the relevant list(s).
 * Internal edges get added to the single list that matches their
 * srp_edge.
 * A cross edge (u,v) instead gets split and added to two lists:
 * one for the (u, y) edge and another for the (x, v) edge.
*)
let map_edges_to_parts partitions (edge, srp_edge) =
  let add_edge j partition =
    match srp_edge with
    | Internal i' ->
      { partition with
        edges = (if i' = j then edge :: partition.edges else partition.edges)
      }
    | Cross (i1, i2) ->
      let u, v = edge in
      (* output case *)
      if i1 = j
      then
        { partition with
          outputs = VertexMap.modify_def [] u (List.cons (edge, [])) partition.outputs
        }
      else if (* input case *)
              i2 = j
      then (
        (* construct the record of the new input information: used when creating the
         * symbolic variable and the require predicate *)
        (* let hyp_var = Var.fresh (Printf.sprintf "hyp_%s" (Edge.to_string old_edge)) in *)
        let input_exp = { edge; var_names = [edge_to_hyp edge]; rank = i1; preds = [] } in
        { partition with
          inputs = VertexMap.modify_def [] v (List.cons input_exp) partition.inputs
        })
      else (* neither case, skip edge and continue *)
        partition
  in
  List.mapi add_edge partitions
;;

(** Map each edge in edges to a partitioned_srp based on where its endpoints lie. *)
let divide_edges (edges : Edge.t list) (node_srps : int VertexMap.t) npartitions
    : partitioned_srp list
  =
  (* invert the node_srps map: divide the vertices into kept and cut for each partition *)
  let partitioned_srp_from_nodes i =
    let kept, cut_mask =
      VertexMap.fold
        (fun v j (k, c) -> (if i = j then v :: k else k), (i = j) :: c)
        node_srps
        ([], [])
    in
    (* reverse the created lists to switch the order back *)
    { rank = i
    ; nodes = List.rev kept
    ; edges = []
    ; cut_mask (* = List.rev cut_mask *)
    ; inputs = VertexMap.empty
    ; outputs = VertexMap.empty
    }
  in
  let initial = List.init npartitions partitioned_srp_from_nodes in
  let new_edges = List.map (fun e -> e, get_srp_edge e node_srps) edges in
  List.fold_left map_edges_to_parts initial new_edges
;;

(** Generate a list of partitioned_srp from the given list of nodes and edges,
 * along with their partitioning function and interface function.
*)
let partition_edges (graph : AdjGraph.t) (partf : Vertex.t -> int) =
  let node_srp_map, max_partition = map_vertices_to_parts graph partf in
  (* add 1 to max_partition to convert from max partition # to number of SRPS *)
  divide_edges (AdjGraph.edges graph) node_srp_map (max_partition + 1)
;;

(** Helper function to extract the partition index
 *  from the partition expression.
 *  Will fail if the partition expression does not return
 *  an int index when given a node.
*)
let interp_partition parte node : int =
  let value = Nv_interpreter.Interp.apply empty_env (deconstructFun parte) (vnode node) in
  int_of_val value |> Option.get
;;

(** Return a list of partitions from the given declarations.
 *  Assumes that the declarations contain a partition decl,
 *  a nodes and an edges decl.
 *  Will fail if the partition decl does not return an int
 *  when given a node.
 *)
let partition_declarations ?(which = None) decls : partitioned_srp list =
  let partition = get_partition decls in
  match partition with
  | Some part ->
    let graph = get_graph decls |> Option.get in
    let partf = interp_partition part in
    let srps = partition_edges graph partf in
    (match which with
    | Some filt -> List.filteri (fun i _ -> Set.mem i filt) srps
    | None -> srps)
  | None -> failwith "no partition expression found!"
;;
