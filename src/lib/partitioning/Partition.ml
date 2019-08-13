open Batteries
open Nv_datastructures

type s = int

let is_cross_partition (f: AdjGraph.Vertex.t -> int) edge =
  (f (fst edge)) <> (f (snd edge))

module Interface(S: Interfaces.OrderedType) :
  sig
    type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * S.t  option

    val create : AdjGraph.Edge.t -> S.t option -> t

    val compare : t -> t -> int
  end =
struct
  type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * S.t option

  let create (edge: AdjGraph.Edge.t) (hyp: S.t option) = (fst edge, snd edge, hyp)

  let compare (u1, v1, h1) (u2, v2, h2) =
    if compare u1 u2 <> 0 then compare u1 u2
    else if compare v1 v2 <> 0 then compare v1 v2
    else compare h1 h2
end

(* module type OrderedInterface = Interfaces.OrderedType Interface.t *)

module InterfaceSet(S: Interfaces.OrderedType) : Set.S with type elt = Interface(S).t = Set.Make(Interface(S))

(* It is possible that a better implementation involves building a new graph using the interface set,
 * as indexing newly-added nodes could break on AdjGraph implementation change
 *)

(* let partition_graph graph interfaces = *)
(*   Set.fold (fun e g -> partition_edge g e) interfaces graph *)
