open Batteries
open Nv_datastructures
open Nv_utils.PrimitiveCollections
open Nv_lang.Syntax
open TransformDecls
open Nv_interpreter

let is_cross_partition (f: AdjGraph.Vertex.t -> 'a) edge =
  (f (fst edge)) <> (f (snd edge))

module Make_interface(S: Interfaces.OrderedType) :
  sig
    type hyp = S.t option
    type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * hyp

    val create : AdjGraph.Edge.t -> S.t option -> t

    val compare : t -> t -> int
  end =
struct
  type hyp = S.t option
  type t = AdjGraph.Vertex.t * AdjGraph.Vertex.t * hyp

  let create (edge: AdjGraph.Edge.t) (hyp: hyp) = (fst edge, snd edge, hyp)

  let compare (u1, v1, h1) (u2, v2, h2) =
    if compare u1 u2 <> 0 then compare u1 u2
    else if compare v1 v2 <> 0 then compare v1 v2
    else compare h1 h2
end

(* module type OrderedInterface = Interfaces.OrderedType Interface.t *)

module Val =
struct
  type t = value
  let compare = compare_values
end

module InterfaceSet : Set.S with type elt = Make_interface(Val).t = Set.Make(Make_interface(Val))

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

let partition_interface (partition: exp option) (interface: exp option) (graph: AdjGraph.t) : InterfaceSet.t =
  match partition with
  | Some parte -> begin
    match interface with
    (* Add each cross-partition edge to the interface *)
    | Some intfe -> 
        let get_edge_hyp u v set = 
          (* partition testing function *)
          let partf_app node = Interp.apply empty_env (deconstructFun parte) (vnode node) in
          (* interface hypothesis *)
          let intf_app = Interp.apply empty_env (deconstructFun intfe) (vedge (u, v)) in
          if (is_cross_partition partf_app (u, v)) then
            InterfaceSet.add (u, v, Some intf_app) set
          else
            set
        in
        AdjGraph.fold_edges get_edge_hyp graph InterfaceSet.empty
    (* Mark every edge as to be inferred *)
    | None -> AdjGraph.fold_edges (fun u v s -> InterfaceSet.add (u, v, None) s) graph InterfaceSet.empty
  end
  | None -> InterfaceSet.empty

let open_network (net: network) : onetwork =
  let { attr_type; init; trans; merge; assertion; partition; interface; symbolics; defs; utys; requires; graph } : network = net
  in
  let ograph = OpenAdjGraph.from_graph graph in
  (* TODO: generate interface set, update ograph *)
  let part_int = partition_interface partition interface graph in
  {
    attr_type;
    init = transform_init init ograph; (*TODO: use actual hypotheses from InterfaceSet *)
    trans = transform_trans trans ograph;
    merge = transform_merge merge ograph;
    assertion;
    symbolics;
    defs;
    utys;
    requires;
    ograph;
  }
