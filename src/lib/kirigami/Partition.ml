open Batteries
open Nv_datastructures
open Nv_utils.PrimitiveCollections
open Nv_lang.Syntax

type s = int

let is_cross_partition (f: AdjGraph.Vertex.t -> int) edge =
  (f (fst edge)) <> (f (snd edge))

module Make_interface(S: Interfaces.OrderedType) :
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

module InterfaceSet : Set.S with type elt = Make_interface(Int).t = Set.Make(Make_interface(Int))

(* It is possible that a better implementation involves building a new graph using the interface set,
 * as indexing newly-added nodes could break on AdjGraph implementation change
 *)
type onetwork =
  {
    attr_type       : ty;
    init            : exp;
    trans           : exp;
    merge           : exp;
    assertion       : exp option;
    symbolics       : (var * ty_or_exp) list;
    defs            : (var * ty option * exp) list;
    utys            : (ty StringMap.t) list;
    requires        : exp list;
    ograph          : OpenAdjGraph.t
  }

let open_network (net: network) : onetwork =
  let { attr_type; init; trans; merge; assertion; partition; interface; symbolics; defs; utys; requires; graph } : network = net
  in
  {
    attr_type;
    init;
    trans;
    merge;
    assertion;
    symbolics;
    defs;
    utys;
    requires;
    ograph = OpenAdjGraph.from_graph graph;
  }

let partition_interface { partition: exp option; interface: exp option; _ } : InterfaceSet.t =
  match partition with
  | Some parte -> match interface with
    | Some intfe -> 
        (* apply the interface expression to each edge that is cross partition *)
        failwith "TODO"
    | None -> failwith "TODO"
  | None -> InterfaceSet.empty
