open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph

type t = {
  graph: AdjGraph.t;
  inputs: Vertex.t VertexMap.t;
  outputs: Vertex.t VertexMap.t;
  broken: Vertex.t VertexMap.t
}

let from_graph (graph: AdjGraph.t) : t =
  { graph;
    inputs = VertexMap.empty;
    outputs = VertexMap.empty;
    broken = VertexMap.empty
  }

let add_new_input (ograph: t) (v: Vertex.t) : t =
  let { graph; inputs; outputs; broken } = ograph in
  good_vertex graph v ;
  (* get the id of the new input *)
  let input = (Vertex.from_index (num_vertices graph)) in
  { graph = add_vertices graph 1 |>
  (fun g -> add_edge g (input, v));
    inputs = VertexMap.add input v inputs;
    outputs = outputs;
    broken = broken }

let add_new_output (ograph: t) (v: Vertex.t) : t =
  let { graph; inputs; outputs; broken } = ograph in
  good_vertex graph v ;
  (* get the id of the new output *)
  let output = (Vertex.from_index (num_vertices graph)) in
  { graph = add_vertices graph 1 |>
  (fun g -> add_edge g (v, output));
    inputs = inputs;
    outputs = VertexMap.add output v outputs;
    broken = broken }

let break_edge (ograph: t) (e: Edge.t) : t =
  let { graph; inputs; outputs; broken } = ograph in
  let (startv, endv) = e in
  { graph = remove_edge graph e;
    inputs = inputs;
    outputs = outputs;
    broken = VertexMap.add startv endv broken
  }

(* Perform a sequence of three updates: add an output, add an input, remove the old edge *)
let partition_edge (ograph: t) (e: Edge.t) : t =
  let (u, v) = e in
    add_new_output ograph u
    |> (fun og -> add_new_input og v)
    |> (fun og -> break_edge og e)

(** Perform a sequence of edge partitionings *)
let partition_graph (ograph: t) (es: EdgeSet.t) : t =
  EdgeSet.fold (fun e g -> partition_edge g e) es ograph

(** Return the base node associated with the input node v, or Not_found *)
let to_node ograph v = VertexMap.find v ograph.inputs

(** Return the base node associated with the output node v, or Not_found *)
let from_node ograph v = VertexMap.find v ograph.outputs

let input_nodes ograph = VertexMap.keys ograph.inputs

let output_nodes ograph = VertexMap.keys ograph.outputs
