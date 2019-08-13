open Batteries
open Nv_datastructures
open Nv_datastructures.AdjGraph

module AuxEdges : Set.S with type elt = AdjGraph.Edge.t = Set.Make(AdjGraph.Edge)

type t =
  { g: AdjGraph.t
  ; inputs: Vertex.t AdjGraph.VertexMap.t
  ; outputs: Vertex.t AdjGraph.VertexMap.t
  }

let add_new_in (ograph: t) (v: AdjGraph.Vertex.t) : t =
  let { g; inputs; outputs } = ograph in
  good_vertex g v ;
  let input = (AdjGraph.Vertex.from_index (num_vertices g)) in
  { g = add_vertices g 1 |>
  (fun g -> add_edge g (input, v));
    inputs = VertexMap.add input v inputs;
    outputs = outputs }
  (* TODO: update inputs map *)

let add_new_out ograph v =
  let { g; inputs; outputs } = ograph in
  good_vertex g v ;
  let output = (AdjGraph.Vertex.from_index (num_vertices g)) in
  { g = add_vertices g 1 |>
  (fun g -> add_edge g (v, output));
    inputs = inputs;
    outputs = VertexMap.add output v outputs }
  (* TODO: update outputs map *)

let partition_edge ograph e =
  let (u, v) = e in
    let og = add_new_out ograph u
    |> (fun og -> add_new_in og v)
    in
      { og with g = (AdjGraph.remove_edge og.g (u,v)) }

(** Return the base node associated with the input node v, or Not_found *)
let to_node ograph v = VertexMap.find v ograph.inputs

(** Return the base node associated with the output node v, or Not_found *)
let from_node ograph v = VertexMap.find v ograph.outputs
