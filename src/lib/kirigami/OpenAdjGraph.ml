open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph

type vertex_vertex_map = Vertex.t VertexMap.t

type interfaces = {
  inputs: vertex_vertex_map;
  outputs: vertex_vertex_map;
  broken: vertex_vertex_map;
}

let intf_empty = {
  inputs = VertexMap.empty;
  outputs = VertexMap.empty;
  broken = VertexMap.empty;
}

type t = AdjGraph.t * interfaces

(** Return the base node associated with the input node v, or Not_found *)
let to_node (intf: interfaces) v = VertexMap.find v intf.inputs

(** Return the base node associated with the output node v, or Not_found *)
let from_node (intf: interfaces) v = VertexMap.find v intf.outputs

(** Return the original edge associated with the output node v, or Not_found *)
let broken_edge (intf: interfaces) v : Edge.t = 
  let u = VertexMap.find v intf.broken in
    (from_node intf v, to_node intf u)

let add_new_input (graph: AdjGraph.t) (intf: interfaces) (v: Vertex.t) : (t * Vertex.t) =
  (* get the id of the new input *)
  (* NOTE: this operation is not parallelizable *)
  let input = (nb_vertex graph) in
  (add_edge (add_vertex graph input) input v,
  { intf with inputs = VertexMap.add input v intf.inputs }),
  input

let add_new_output (graph: AdjGraph.t) (intf: interfaces) (v: Vertex.t) : (t * Vertex.t) =
  (* get the id of the new output *)
  let output = (nb_vertex graph) in
  (add_vertex graph output |> (fun g -> add_edge g v output),
  { intf with outputs = VertexMap.add output v intf.outputs }),
  output

let break_out_in_edge (graph: AdjGraph.t) (intf: interfaces) (outnode: Vertex.t) (innode: Vertex.t) : t =
  remove_edge graph (from_node intf outnode) (to_node intf innode),
  { intf with broken = VertexMap.add outnode innode intf.broken
  }

let input_nodes intf = VertexMap.keys intf.inputs

let output_nodes intf = VertexMap.keys intf.outputs

(* Perform a sequence of three updates: add an output, add an input, remove the old edge *)
let partition_edge (g: AdjGraph.t) (intf: interfaces) (e: Edge.t) : (AdjGraph.t * interfaces) =
  let (u, v) = e in
  let ((g, intf), outnode) = add_new_output g intf u in
  let ((g, intf), innode) = add_new_input g intf v in
  break_out_in_edge g intf outnode innode

(** Perform a sequence of edge partitionings *)
let partition_graph (g: AdjGraph.t) (intf: interfaces) (es: EdgeSet.t) : (AdjGraph.t * interfaces) =
  EdgeSet.fold (fun e (g, i) -> partition_edge g i e) es (g, intf)

(** Map each vertex in the  list of vertices to a number.
 *  Return the map and the highest number computed.
 *)
let map_vertices_to_parts vertices (partf: Vertex.t -> int) : (int VertexMap.t * int) =
  let add_vertex (m, a) v =
    let vnum = partf v in
    (* add the vertex and its mapping,
     * and increase the map number if it is the new largest mapping *)
    (VertexMap.add v vnum m, max vnum a)
  in
  List.fold_left add_vertex (VertexMap.empty, 0) vertices

(** Return a list of [n] lists of vertices, divided according to their mappings.
 *  The index of the old index in the returned list corresponds to its new index
 *  in the partitioned network.
 *)
let divide_vertices vmap nlists =
  let initial = List.make nlists []
  in
  (* add the vertex to the corresponding list *)
  let update_list v ix l =
    List.mapi (fun lix a -> if (lix = ix) then v :: a else a) l
  in
  (* flip each sublist back so that the nodes are in ascending order *)
  List.map (fun l -> List.rev l) (VertexMap.fold update_list vmap initial)

(* Type for distinguishing cross edges from internal edges *)
type srp_edge_index =
  | Internal of int
  | Cross of int * int

(** Return the remapped form of the given edge along with Some SRP.
 *  If the new edge is cross-partition, return None as the SRP.
 *)
let remap_edge edge (vlists: Vertex.t list list) =
  let (u, v) = edge in
  let find_endpoint v =
    List.hd (List.filteri_map 
    (fun j l -> Option.map (fun i -> (i, j)) (List.index_of v l)) vlists)
  in
  let (newu, usrp) = find_endpoint u in
  let (newv, vsrp) = find_endpoint v in
  if (usrp != vsrp) then 
    (* cross-partition case *)
    ((newu, newv), Cross (usrp, vsrp))
  else
    ((newu, newv), Internal usrp)

type interfaces_alt = {
  inputs: vertex_vertex_map;
  outputs: vertex_vertex_map;
  outs_broken: Edge.t VertexMap.t;
  broken_ins: Vertex.t EdgeMap.t;
}

let intf_alt_empty : interfaces_alt = {
  inputs = VertexMap.empty;
  outputs = VertexMap.empty;
  outs_broken = VertexMap.empty;
  broken_ins = EdgeMap.empty;
}

(** Map each edge in edges to one of the lists of lists, based on
 *  where its endpoints lie.
 *)
let divide_edges (edges: Edge.t list) (vlists: Vertex.t list list) : ((int * Edge.t list * interfaces_alt) list) =
  (* Set up initial: each index has:
   * - an int indicating # of nodes,
   * - a list of edges,
   * - an interfaces struct
   * Cf. repr of an OpenAdjGraph.t
   *)
  let initial = List.map (fun l -> (List.length l, [], intf_alt_empty)) vlists in
  let new_edges = List.map (fun e -> remap_edge e vlists) edges in
  (* map the (e, i) pair to the corresponding list *)
  let map_edges_to_lists list_of_lists (edge, i) : (int * Edge.t list * interfaces_alt) list = 
    (* Add the edge to the relevant list(s).
     * Internal edges get added to the single list that matches their 
     * srp_edge_index.
     * A cross edge (u,v) instead gets split and added to two lists:
     * one for the (u, y) edge and another for the (x, v) edge.
     *)
    let add_edge j (nodes, list_of_edges, intf) : (int * Edge.t list * interfaces_alt) = match i with
      | Internal i' -> if i' = j then (nodes, edge :: list_of_edges, intf) else (nodes, list_of_edges, intf)
      | Cross (i1, i2) -> begin 
        let (u, v) = edge in
        (* output case *)
        if i1 = j then 
          (* new node number *)
          let outnode = nodes in
          let new_intf = {
            intf with outputs = VertexMap.add outnode u intf.outputs;
                      outs_broken = VertexMap.add outnode edge intf.outs_broken;
          }
          in (nodes + 1, (Edge.create u () outnode) :: list_of_edges, new_intf)
        else 
          (* input case *)
          if i2 = j then
          (* new node number *)
          let innode = nodes in
          let new_intf = {
            intf with inputs = VertexMap.add innode v intf.inputs;
                      broken_ins = EdgeMap.add edge innode intf.broken_ins;
          }
          in (nodes + 1, (Edge.create innode () v) :: list_of_edges, new_intf)
          (* neither case, continue *)
          else (nodes, list_of_edges, intf)
      end
    in
    List.mapi add_edge list_of_lists
  in
  List.map (fun (n, l, intf) -> (n, List.rev l, intf)) (List.fold_left map_edges_to_lists initial new_edges)

(* How to create new node-edge groups
 * 1. Get original nodes and edges
 * 2. Map each node through partition to get its new SRP
 * 3. Create a map from each old node index to its new index starting from 0.
 * 4. Map each edge using the node map to its new SRP,
 *    or if it's cross-partition, to a new output-input pair
 * 5. Add edges according to the old-new node renaming map.
 *)
let partition_edges (nodes: Vertex.t list) (edges: Edge.t list) (partf: Vertex.t -> int) =
  let (node_srp_map, num_srps) = map_vertices_to_parts nodes partf in
  let divided_nodes = divide_vertices node_srp_map (num_srps + 1) in
  divide_edges edges divided_nodes

