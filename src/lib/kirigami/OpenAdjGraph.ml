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
let compose_edge (graph: AdjGraph.t) (intf: interfaces) (outnode: Vertex.t) (innode: Vertex.t) : (AdjGraph.t * interfaces) =
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
