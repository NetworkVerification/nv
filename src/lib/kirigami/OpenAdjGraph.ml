open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph

type vertex_vertex_map = Vertex.t VertexMap.t

type t = {
  graph: AdjGraph.t;
  inputs: vertex_vertex_map;
  outputs: vertex_vertex_map;
  broken: vertex_vertex_map;
}

let from_graph (graph: AdjGraph.t) : t =
  { graph;
    inputs = VertexMap.empty;
    outputs = VertexMap.empty;
    broken = VertexMap.empty
  }

(** Return the base node associated with the input node v, or Not_found *)
let to_node ograph v = VertexMap.find v ograph.inputs

(** Return the base node associated with the output node v, or Not_found *)
let from_node ograph v = VertexMap.find v ograph.outputs

(** Return the original edge associated with the output node v, or Not_found *)
let broken_edge ograph v : Edge.t = 
  let u = VertexMap.find v ograph.broken in
    (from_node ograph v, to_node ograph u)

let add_new_input (ograph: t) (v: Vertex.t) : (t * Vertex.t) =
  let { graph; inputs; outputs; broken } = ograph in
  good_vertex graph v ;
  (* get the id of the new input *)
  (* NOTE: this operation is not parallelizable *)
  let input = (Vertex.create (nb_vertex graph)) in
  { graph = add_vertex graph input |>
  (fun g -> add_edge g input v);
    inputs = VertexMap.add input v inputs;
    outputs = outputs;
    broken = broken }, input

let add_new_output (ograph: t) (v: Vertex.t) : (t * Vertex.t) =
  let { graph; inputs; outputs; broken } = ograph in
  good_vertex graph v ;
  (* get the id of the new output *)
  let output = (Vertex.create (nb_vertex graph)) in
  { graph = add_vertex graph output |>
  (fun g -> add_edge g v output);
    inputs = inputs;
    outputs = VertexMap.add output v outputs;
    broken = broken }, output

let break_out_in_edge (ograph: t) (outnode: Vertex.t) (innode: Vertex.t) : t =
  let { graph; inputs; outputs; broken } = ograph in
  { graph = remove_edge graph (from_node ograph outnode) (to_node ograph innode);
    inputs = inputs;
    outputs = outputs;
    broken = VertexMap.add outnode innode broken
  }

let input_nodes ograph = VertexMap.keys ograph.inputs

let output_nodes ograph = VertexMap.keys ograph.outputs

(* Perform a sequence of three updates: add an output, add an input, remove the old edge *)
let partition_edge (ograph: t) (e: Edge.t) : t =
  let (u, v) = e in
  let (og, outnode) = add_new_output ograph u in
  let (og, innode) = add_new_input og v in
  break_out_in_edge og outnode innode

(** Perform a sequence of edge partitionings *)
let partition_graph (ograph: t) (es: EdgeSet.t) : t =
  EdgeSet.fold (fun e g -> partition_edge g e) es ograph

(* Perform a sequence of three updates: remove an output, remove an input, add an edge *)
let compose_edge (ograph: t) (outnode: Vertex.t) (innode: Vertex.t) : t =
  let u = from_node ograph outnode in
  let v = to_node ograph innode in
  (* Perform the updates to the internal graph *)
  let update_graph g =
    remove_vertex g outnode |>
    (fun g -> remove_vertex g innode) |>
    (fun g -> add_edge g u v)
  in
  {
    graph = update_graph ograph.graph;
    inputs = begin
      ignore (VertexMap.remove innode ograph.inputs); ograph.inputs
    end;
    outputs = begin
      ignore (VertexMap.remove outnode ograph.outputs); ograph.outputs
    end;
    broken = begin
      ignore (VertexMap.remove outnode ograph.broken); ograph.broken
    end;
  }
