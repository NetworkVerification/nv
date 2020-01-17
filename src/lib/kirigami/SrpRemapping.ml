(* Convert all edges and nodes in the program to new values,
   after the SRP has been split *)
open Nv_datastructures.AdjGraph
open Nv_lang.Syntax

(** A type for keeping track of the input to base and output to base relationships. *)
type interface = {
  (* Key: input node, value: base node *)
  inputs: Vertex.t VertexMap.t
  (* Key: output node, value: base node *)
  outputs: Vertex.t VertexMap.t;
}

let empty_interface : interface = {
  inputs = VertexMap.empty;
  outputs = VertexMap.empty;
}

(** A type for transforming the declarations over the old SRP
 *  to declarations for the new partitioned SRP.
 *  The nodes and edges maps help us to remap nodes and edges.
 *  If an old node or edge is not a value in the map,
 *  then we know it has been removed and we can drop it from
 *  the SRP.
 *  The predicates help us keep track of the `interface` predicates
 *  associated with a given new edge, since both inputs and outputs
 *  have associated predicates (required on the hypotheses and 
 *  asserted on the output solutions, respectively).
 *)
type partitioned_srp = {
  (* the number of nodes in the network *)
  nodes: int,
  (* the edges in the network *)
  edges: Edge.t list,
  (* keys are old nodes, values are Some new node or None *)
  node_map: (Vertex.t option) VertexMap.t
  (* keys are old edges, values are Some new edge or None *)
  edge_map: (Edge.t option) EdgeMap.t
  intf: interface;
  preds: Syntax.exp EdgeMap.t
}

let create_partitioned_srp nodes edges node_map edge_map intf preds =
  { nodes; edges; node_map; edge_map; intf; preds; }

(** Map each vertex in the list of vertices to a partition number.
 *  Return the map and the number of partitions.
 *)
let map_vertices_to_parts vertices (partf: Vertex.t -> int) : (int VertexMap.t * int) =
  let add_vertex (m, a) v =
    let vnum = partf v in
    (* add the vertex and its partition mapping,
     * and increase the map number if it is the new largest mapping *)
    (VertexMap.add v vnum m, max vnum a)
  in
  List.fold_left add_vertex (VertexMap.empty, 0) vertices

(** Return a list of [n] maps from old vertices to new vertices,
 *  divided according to their mappings, along with the number of new vertices
 *  in each.
 *  If an old vertex u is found in a given SRP, then its value will
 *  be Some v, where v is the new name for u.
 *  If not, its value will be None.
 *)
let divide_vertices vmap nlists : (int * (Vertex.t VertexMap.t)) list =
  let initial = List.make nlists (0, VertexMap.empty)
  in
  (* add the vertex to the corresponding map and set it to None elsewhere *)
  let update_maps vertex srp_ix (n, vmaps) =
    List.mapi (fun lix a -> 
      (n + if (lix = srp_ix) then 1 else 0,
      VertexMap.add a (if (lix = srp_ix) then Some lix else None) vmaps))
  in
  VertexMap.fold update_maps vmap initial


(* Type for distinguishing cross edges from internal edges *)
type srp_edge =
  (* Internal i: represents an edge internal to an SRP [i] *)
  | Internal of int
  (* Cross i j: represents an edge that crosses from SRP [i] to SRP [j] *)
  | Cross of int * int

(** Return the remapped form of the given edge along with the SRPs it belongs to.
 *)
let remap_edge edge (vmaps: Vertex.t VertexMap.t list) : (Edge.t * srp_edge) =
  let (u, v) = edge in
  (* For the given old vertex, find the associated new vertex *)
  let find_endpoint vertex =
    let wrap_srp j = Option.map (fun i -> (i, j)) in
    let found = (List.filteri_map (fun j m -> wrap_srp (VertexMap.find_default None vertex m)) vmaps) in
    assert (List.length found 1);  (* only one SRP should contain the endpoint *)
    List.hd found
  in
  let (newu, usrp) = find_endpoint u in
  let (newv, vsrp) = find_endpoint v in
  if (usrp != vsrp) then 
    (* cross-partition case *)
    ((newu, newv), Cross (usrp, vsrp))
  else
    ((newu, newv), Internal usrp)

(** Add the edge to the relevant list(s).
 * Internal edges get added to the single list that matches their 
 * srp_edge.
 * A cross edge (u,v) instead gets split and added to two lists:
 * one for the (u, y) edge and another for the (x, v) edge.
 *)
let map_edges_to_parts predf partitions (old_edge, (edge, srp_edge)) =
  let add_edge j partition =
    match srp_edge with
    | Internal i' -> {
      partition with edge_map = EdgeMap.add old_edge (if i' = j then Some edge else None) partition.edge_map;
    }
    | Cross (i1, i2) -> begin
      let pred = predf old_edge in
      let (u, v) = edge in
      (* output case *)
      if i1 = j then
        (* new node number *)
        let outnode = nodes in
        let new_edge = Edge.create u () outnode in
        let new_intf : interfaces_alt = {
          intf with outputs = VertexMap.add outnode u intf.outputs;
        }
        in {
          partition with nodes = partition.nodes + 1;
                         edges = new_edge :: partition.edges;
                         edge_map = EdgeMap.add old_edge (Some new_edge) partition.edge_map;
                         intf = new_intf;
                         preds = EdgeMap.add new_edge pred preds;
        }
      else
        (* input case *)
        if i2 = j then
        (* new node number *)
        let innode = nodes in
        let new_edge = Edge.create innode () v in
        let new_intf = {
          intf with inputs = VertexMap.add innode v intf.inputs;
        }
        in {
          partition with nodes = partition.nodes + 1;
                         edges = new_edge :: partition.edges;
                         edge_map = EdgeMap.add old_edge (Some new_edge) partition.edge_map;
                         intf = new_intf;
                         preds = EdgeMap.add new_edge pred preds;
        }
        (* neither case, mark edge as absent and continue *)
        else {
          partition with edge_map = EdgeMap.add old_edge None partition.edge_map;
        }
    end
  in
  List.mapi add_edge partitions

(** Map each edge in edges to a map from it to a new edge, based on
 *  where its endpoints lie.
 *)
let divide_edges (edges: Edge.t list) (predf: Edge.t -> Syntax.exp) (vlists: Vertex.t list list) : (partitioned_srp list) =
  (* Set up initial: each index has:
   * - an int indicating # of nodes,
   * - a list of edges,
   * - an interfaces struct
   * Cf. repr of an OpenAdjGraph.t
   *)
  let initial = List.map (fun l -> create_partitioned_srp (List.length l, [], VertexMap.empty, VertexMap.empty, intf_empty, EdgeMap.empty)) vlists in (* FIXME: may not use vlists anymore here *)
  let new_edges = List.map (fun e -> (e, remap_edge e vlists)) edges in
  let mapped = List.fold_left (map_edges_to_lists predf) initial new_edges in
  List.map (fun (n, l, intf, preds) -> create_partitioned_srp n (List.rev l) intf preds) mapped
