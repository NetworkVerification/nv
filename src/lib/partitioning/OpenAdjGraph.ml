open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph

type t = {
  graph: AdjGraph.t;
  inputs: Vertex.t VertexMap.t;
  outputs: Vertex.t VertexMap.t;
}

let add_new_input (ograph: t) (v: AdjGraph.Vertex.t) : t =
let { graph; inputs; outputs } = ograph in
good_vertex graph v ;
(* get the id of the new input *)
let input = (AdjGraph.Vertex.from_index (num_vertices graph)) in
{ graph = add_vertices graph 1 |>
(fun g -> add_edge g (input, v));
  inputs = VertexMap.add input v inputs;
  outputs = outputs }

let add_new_output (ograph: t) (v: Vertex.t) : t =
let { graph; inputs; outputs } = ograph in
good_vertex graph v ;
(* get the id of the new output *)
let output = (AdjGraph.Vertex.from_index (num_vertices graph)) in
{ graph = add_vertices graph 1 |>
(fun g -> add_edge g (v, output));
  inputs = inputs;
  outputs = VertexMap.add output v outputs }

let partition_edge (ograph: t) (e: Edge.t) : t =
let (u, v) = e in
  let og = add_new_output ograph u
  |> (fun og -> add_new_input og v)
  in
    { og with graph = (AdjGraph.remove_edge og.graph (u,v)) }

(** Return the base node associated with the input node v, or Not_found *)
let to_node ograph v = VertexMap.find v ograph.inputs

(** Return the base node associated with the output node v, or Not_found *)
let from_node ograph v = VertexMap.find v ograph.outputs

let input_nodes ograph = VertexMap.keys ograph.inputs

let output_nodes ograph = VertexMap.keys ograph.outputs
