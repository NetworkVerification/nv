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

(* Perform a sequence of three updates: remove an output, remove an input, add an edge *)
let compose_edge graph intf outnode innode : (AdjGraph.t * interfaces) =
  let u = from_node intf outnode in
  let v = to_node intf innode in
  (* Perform the updates to the internal graph *)
  let update_graph g =
    remove_vertex g outnode |>
    (fun g -> remove_vertex g innode) |>
    (fun g -> add_edge g u v)
  in
  update_graph graph,
  {
    inputs = begin
      ignore (VertexMap.remove innode intf.inputs); intf.inputs
    end;
    outputs = begin
      ignore (VertexMap.remove outnode intf.outputs); intf.outputs
    end;
    broken = begin
      ignore (VertexMap.remove outnode intf.broken); intf.broken
    end;
  }

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

(** Create a list by inserting the given element the given number
 * of times.
 *)
let repeat elem times =
  let rec aux e n l =
    if n = 0 then e :: l else aux e (n - 1) (e :: l)
  in
  aux elem times []

(** Return a list of [n] lists of vertices, divided according to their mappings.
 *  The index of the old index in the returned list corresponds to its new index
 *  in the partitioned network.
 *)
let divide_vertices vmap nlists =
  let initial = repeat [] nlists
  in
  (* add the vertex to the corresponding list *)
  let update_list v ix l =
    List.rev @@ List.mapi (fun lix a -> if (lix = ix) then v :: a else a) l
  in
  VertexMap.fold update_list vmap initial

(** Return the remapped form of the given edge along with Some SRP.
 *  If the new edge is cross-partition, return None as the SRP.
 *)
let remap_edge edge (vlists: Vertex.t list list) =
  let (u, v) = edge in
  (* get the first *)
  let find_endpoint v =
    List.hd (List.filteri_map 
    (fun i l -> Option.map (fun j -> (i, j)) (List.index_of v l)) vlists)
  in
  let (newu, usrp) = find_endpoint u in
  let (newv, vsrp) = find_endpoint v in
  if (usrp != vsrp) then 
    (* cross-partition case *)
    ((newu, newv), None)
  else
    ((newu, newv), Some usrp)

(** Map each edge in edges to one of the lists of lists, based on
 *  where its endpoints lie.
 *)
let divide_edges (edges: Edge.t list) (vlists: Vertex.t list list) =
  let initial = repeat [] (List.length vlists) in
  let new_edges = List.map (fun e -> remap_edge e vlists) edges in
  (* map the (e, i) pair to the corresponding list *)
  let map_edges_to_lists l (e, i) = 
    (* TODO: handle None (cross-partition) case *)
    List.rev @@ List.mapi (fun j a -> if (i = Some j) then e :: a else a) l
  in
  List.fold_left map_edges_to_lists initial new_edges

(* How to create new node-edge groups
 * 1. Get original nodes and edges
 * 2. Map each node through partition to get its new SRP
 * 3. Create a map from each old node index to its new index starting from 0.
 * 4. Map each edge using the node map to its new SRP,
 *    or if it's cross-partition, to a new output-input pair
 * 5. Add edges according to the old-new node renaming map.
 *)
