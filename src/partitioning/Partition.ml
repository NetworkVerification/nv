open Batteries
let Graph = open AdjGraph

let is_cross_partition (f: Graph.Edge.t -> int) edge =
  (f (fst edge)) <> (f (snd edge))

module Interface = struct
  type t = Graph.Vertex.t * Graph.Vertex.t * hypothesis int
end

module InterfaceSet = Set.Make(Interface)

(* Possible hypotheses used when annotating interface edges *)
type hypothesis =
  | None (* edge is not cross-partition *)
  | Infer (* infer the input's hypothesis, starting from a default *)
  | Annotate of t (* use the given attribute as the input's hypothesis *)

let hyp_to_opt_att hyp = function
  | Annotate t -> Some t
  | Infer -> None
  | None -> None

(* TODO: not yet implemented *)
let partition_edge graph _interface = graph

let partition_graph graph interfaces =
  Set.fold (fun e g -> partition_edge g e) interfaces graph
