open Batteries

type s = int

(* Possible hypotheses used when annotating interface edges *)
type 'a hypothesis =
  | None (* edge is not cross-partition *)
  | Infer (* infer the input's hypothesis, starting from a default *)
  | Annotate of 'a (* use the given attribute as the input's hypothesis *)

let is_cross_partition (f: AdjGraph.Edge.t -> int) edge =
  (f (fst edge)) <> (f (snd edge))

module Interface = struct
  type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * int hypothesis

  let compare (u1, v1, h1) (u2, v2, h2) =
    if compare u1 u2 <> 0 then compare u1 u2
    else if compare v1 v2 <> 0 then compare v1 v2
    else compare h1 h2
end

module InterfaceSet = Set.Make(Interface)

let hyp_to_opt_att hyp = function
  | Annotate t -> Some t
  | Infer -> None
  | None -> None

(* It is possible that a better implementation involves building a new graph using the interface set,
 * as indexing newly-added nodes could break on AdjGraph implementation change
 *)
let partition_edge graph interface =
  let nvertices = AdjGraph.num_vertices graph in
  (* FIXME: does this assume how we index nodes? *)
  let (in_node, out_node) = (nvertices, nvertices + 1) in
  let (u, v, _h) = interface in
  (* add new input and output vertices *)
  AdjGraph.add_vertices graph 2
  |> (fun g -> AdjGraph.remove_edge g (u, v))
  |> (fun g -> AdjGraph.add_edge g (u, out_node))
  |> (fun g -> AdjGraph.add_edge g (in_node, v))


let partition_graph graph interfaces =
  Set.fold (fun e g -> partition_edge g e) interfaces graph
