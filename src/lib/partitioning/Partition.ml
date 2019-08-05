open Batteries
open Nv_datastructures

type s = int

(* Possible hypotheses used when annotating interface edges *)
module Hyp : sig
type 'a t = private
  | None (* edge is not cross-partition *)
  | Infer (* infer the input's hypothesis, starting from a default *)
  | Annotate of 'a (* use the given attribute as the input's hypothesis *)

val annotate : 'a -> 'a t

val infer : 'a t

val none : 'a t
end
=
struct
type 'a t =
  | None
  | Infer
  | Annotate of 'a

let annotate v = (* Checking, logging, etc *) (); Annotate v

let infer = (* etc *) Infer

let none = (* etc *) None

end

let destruct_annotate hyp = match hyp with
  | Hyp.Annotate v -> Some v
  | Hyp.Infer -> None
  | Hyp.None -> None

let is_cross_partition (f: AdjGraph.Vertex.t -> int) edge =
  (f (fst edge)) <> (f (snd edge))

module Interface(S: Interfaces.OrderedType) :
  sig
    type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * S.t  Hyp.t

    val create : AdjGraph.Edge.t -> S.t Hyp.t -> t

    val compare : t -> t -> int

    val partition_edge : AdjGraph.t -> t -> AdjGraph.t
  end =
struct
  type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * S.t Hyp.t

  let create (edge: AdjGraph.Edge.t) (hyp: S.t Hyp.t) = (fst edge, snd edge, hyp)

  let compare (u1, v1, h1) (u2, v2, h2) =
    if compare u1 u2 <> 0 then compare u1 u2
    else if compare v1 v2 <> 0 then compare v1 v2
    else compare h1 h2

  let partition_edge graph interface =
    let (u, v, _h) = interface in
    AdjGraph.add_new_out graph u
    |> (fun g -> AdjGraph.add_new_in g v)
    |> (fun g -> AdjGraph.remove_edge g (u, v))
end

(* module type OrderedInterface = Interfaces.OrderedType Interface.t *)

module InterfaceSet(S: Interfaces.OrderedType) : Set.S with type elt = Interface(S).t = Set.Make(Interface(S))

(* It is possible that a better implementation involves building a new graph using the interface set,
 * as indexing newly-added nodes could break on AdjGraph implementation change
 *)

(* let partition_graph graph interfaces = *)
(*   Set.fold (fun e g -> partition_edge g e) interfaces graph *)
