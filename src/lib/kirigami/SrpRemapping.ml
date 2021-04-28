(* Convert all edges and nodes in the program to new values,
   after the SRP has been split *)
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
  ; (* the variable associated with the input node *)
    var : Var.t
  ; (* the partition rank of the associated output *)
    rank : int
  ; (* the associated predicate expressions: functions over attributes *)
    preds : exp list
  }

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
 **
 ** Invariants:
 ** - every value in node_map and edge_map is a valid node or edge
 **   in the new SRP
 **)
type partitioned_srp =
  { (* the rank of the partitioned srp *)
    rank : int
  ; (* the number of nodes in the network *)
    nodes : int
  ; (* the edges in the network *)
    edges : Edge.t list
  ; (* keys are old nodes, values are Some new node or None *)
    node_map : Vertex.t option VertexMap.t
  ; (* keys are old edges, values are Some new edge or None *)
    edge_map : Edge.t option EdgeMap.t
  ; (* Maps from base nodes to their inputs and outputs *)
    (* the predicate applies to the input node as a `require`
     * on the hypothesis symbolic variable, and to the
     * output node as an `assert` on the solution
     *)
    inputs : input_exp list VertexMap.t
  ; outputs : (Edge.t * exp list) list VertexMap.t
  }

(** Return the number of nodes in the global network. *)
let get_global_nodes parted_srp = VertexMap.cardinal parted_srp.node_map

(** Return a list of nodes which inverts the node_map list to give the old numbering
 ** of the current partition's nodes. *)
let get_old_nodes parted_srp =
  let add_node old_node new_node l =
    match new_node with
    | Some v -> (v, old_node) :: l
    | None -> l
  in
  let pairs = VertexMap.fold add_node parted_srp.node_map [] in
  List.map (fun (_, u) -> u) (List.sort Pervasives.compare pairs)
;;

let string_of_input_exp { var; rank; edge; preds } =
  Printf.sprintf
    "var %s (%d)\n%s: preds %s"
    (Var.to_string var)
    rank
    (Edge.to_string edge)
    (list_to_string Printing.exp_to_string preds)
;;

let string_of_partitioned_srp p =
  let nmap = VertexMap.to_string (ostring string_of_int) p.node_map in
  let output_to_string (e, p) =
    Printf.sprintf
      "%s: preds %s"
      (Edge.to_string e)
      (list_to_string Printing.exp_to_string p)
  in
  let inputs = VertexMap.to_string (list_to_string string_of_input_exp) p.inputs in
  let outputs = VertexMap.to_string (list_to_string output_to_string) p.outputs in
  Printf.sprintf
    "Partition %d: %d nodes, %d edges\nnode_map:%s\ninputs:\n%s\noutputs:\n%s\n"
    p.rank
    p.nodes
    (List.length p.edges)
    nmap
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
let map_vertices_to_parts vertices (partf : Vertex.t -> int) : int VertexMap.t * int =
  let add_vertex (m, a) v =
    let vnum = partf v in
    (* add the vertex and its partition mapping,
     * and increase the map number if it is the new largest mapping *)
    VertexMap.add v vnum m, max vnum a
  in
  List.fold_left add_vertex (VertexMap.empty, 0) vertices
;;

(* A data structure indicating a vertex remapping and giving the number of
 * vertices for which the remapping maps to Some v as opposed to None. *)
type vmap = int * Vertex.t option VertexMap.t

(** Return a list of [n] maps from old vertices to new vertices,
 *  divided according to their mappings, along with the number of new vertices
 *  in each.
 *  If an old vertex u is found in a given SRP, then its value will
 *  be Some v, where v is the new name for u.
 *  If not, its value will be None.
*)
let divide_vertices vmap nlists : vmap list =
  let initial = List.make nlists (0, VertexMap.empty) in
  (* add the vertex to the corresponding map and set it to None elsewhere *)
  let place_vertex vertex srp_ix l =
    List.mapi
      (fun lix (n, vmaps) ->
        ( (n + if lix = srp_ix then 1 else 0)
        , (* the new vertex is the old total number *)
          VertexMap.add vertex (if lix = srp_ix then Some n else None) vmaps ))
      l
  in
  VertexMap.fold place_vertex vmap initial
;;

(* Type for distinguishing cross edges from internal edges *)
type srp_edge =
  (* Internal i: represents an edge internal to an SRP [i] *)
  | Internal of int
  (* Cross i j: represents an edge that crosses from SRP [i] to SRP [j] *)
  | Cross of int * int

(** Return the remapped form of the given edge along with the SRPs it belongs to.
*)
let remap_edge edge (vmaps : vmap list) : Edge.t * srp_edge =
  let u, v = edge in
  (* For the given old vertex, find the associated new vertex *)
  let find_endpoint vertex =
    let wrap_srp j = Option.map (fun i -> i, j) in
    let found =
      List.filteri_map
        (fun j (_, m) -> wrap_srp j (VertexMap.find_default None vertex m))
        vmaps
    in
    assert (List.length found = 1);
    (* only one SRP should contain the endpoint *)
    List.hd found
  in
  let newu, usrp = find_endpoint u in
  let newv, vsrp = find_endpoint v in
  if usrp != vsrp
  then (* cross-partition case *)
    (newu, newv), Cross (usrp, vsrp)
  else (newu, newv), Internal usrp
;;

(** Add the edge to the relevant list(s).
 * Internal edges get added to the single list that matches their
 * srp_edge.
 * A cross edge (u,v) instead gets split and added to two lists:
 * one for the (u, y) edge and another for the (x, v) edge.
*)
let map_edges_to_parts partitions (old_edge, (edge, srp_edge)) =
  let add_edge j partition =
    match srp_edge with
    | Internal i' ->
      { partition with
        edges = (if i' = j then edge :: partition.edges else partition.edges)
      ; edge_map =
          EdgeMap.add old_edge (if i' = j then Some edge else None) partition.edge_map
      }
    | Cross (i1, i2) ->
      let u, v = edge in
      (* output case *)
      if i1 = j
      then
        { partition with
          outputs = VertexMap.modify_def [] u (List.cons (old_edge, [])) partition.outputs
        }
      else if (* input case *)
              i2 = j
      then (
        (* construct the record of the new input information: used when creating the
         * symbolic variable and the require predicate *)
        let hyp_var = Var.fresh (Printf.sprintf "hyp_%s" (Edge.to_string old_edge)) in
        let input_exp = { edge = old_edge; var = hyp_var; rank = i1; preds = [] } in
        { partition with
          inputs = VertexMap.modify_def [] v (List.cons input_exp) partition.inputs
        })
      else
        (* neither case, mark edge as absent and continue *)
        { partition with edge_map = EdgeMap.add old_edge None partition.edge_map }
  in
  List.mapi add_edge partitions
;;

(** Map each edge in edges to a partitioned_srp based on where its endpoints lie. *)
let divide_edges (edges : Edge.t list) (vmaps : vmap list) : partitioned_srp list =
  let partitioned_srp_from_nodes i (nodes, node_map) =
    { rank = i
    ; nodes
    ; edges = []
    ; node_map
    ; edge_map = EdgeMap.empty
    ; inputs = VertexMap.empty
    ; outputs = VertexMap.empty
    }
  in
  let initial = List.mapi partitioned_srp_from_nodes vmaps in
  let new_edges = List.map (fun e -> e, remap_edge e vmaps) edges in
  List.fold_left map_edges_to_parts initial new_edges
;;

(** Generate a list of partitioned_srp from the given list of nodes and edges,
 * along with their partitioning function and interface function.
*)
let partition_edges
    (nodes : Vertex.t list)
    (edges : Edge.t list)
    (partf : Vertex.t -> int)
  =
  let node_srp_map, max_partition = map_vertices_to_parts nodes partf in
  (* add 1 to max_partition to convert from max partition # to number of SRPS *)
  let divided_nodes = divide_vertices node_srp_map (max_partition + 1) in
  divide_edges edges divided_nodes
;;

(** Helper function to extract the partition index
 *  from the partition expression.
*)
let interp_partition parte node : int =
  let value = Nv_interpreter.Interp.apply empty_env (deconstructFun parte) (vnode node) in
  int_of_val value |> Option.get
;;

let partition_declarations decls : partitioned_srp list =
  let partition = get_partition decls in
  match partition with
  | Some part ->
    let nodes = get_nodes decls |> Option.get in
    let node_list = List.range 0 `To (nodes - 1) in
    let edges = get_edges decls |> Option.get in
    let partf = interp_partition part in
    partition_edges node_list edges partf
  | None -> failwith "no partition expression found!"
;;
