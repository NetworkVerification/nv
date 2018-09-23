open Graph
open AbstractionMap
open Unsigned
open Console
open Srp
open Hashtbl
open Syntax

let debugAbstraction = ref true
   
module AbstractNodeSet : Set.S with type elt := AbstractNode.t = Set.Make(AbstractNode)

(* Module packing together a set of nodes and a hash of a routing policy *)
module TransferNodes =
  struct
    (* trans hash, set of nodes*)
    type t = int * AbstractNode.t
    let compare (h1,us1) (h2,us2) =
      if compare h1 h2 = 0 then
          AbstractNode.compare us1 us2
      else
        compare h1 h2
  end

(* Sets of (trans_hash, {nodes}) *)
module TransferNodesSet : Set.S with type elt := TransferNodes.t = Set.Make(TransferNodes)

(* Module packing together a hash of a merge policy and sets of TransferNodes*)
module NodeGroups =
  struct
    (* merge_hash * {(trans_hash, {nodes})}*) 
    type t = int * TransferNodesSet.t
    let compare (h1, p1) (h2, p2) =
      if compare h1 h2 = 0 then
        TransferNodesSet.compare p1 p2
      else
        compare h1 h2
  end
       
module NodeGroupsMap : Map.S with type key := NodeGroups.t = Map.Make(NodeGroups)

(* given a map from concrete vertices to NodeGroups, groupsKeysByValue
   will reverse the mapping creating a map from NodeGroups to set of
   concrete vertices, in effect computing sets of concrete vertices
   that map to the same NodeGroups.*)
let groupKeysByValue (umap: NodeGroups.t VertexMap.t) : AbstractNodeSet.t =
  let reverseMap =
    VertexMap.fold (fun u vs acc ->
        NodeGroupsMap.update vs (fun us -> match us with
                                              | None -> Some (AbstractNode.singleton u)
                                              | Some us -> Some (AbstractNode.add u us)) acc)
                   umap NodeGroupsMap.empty in
  NodeGroupsMap.fold (fun _ v acc -> AbstractNodeSet.add v acc)
                     reverseMap AbstractNodeSet.empty  

(* This does not handle a forall-forall abstraction, it's trivial to fix that *)
let refineAbstraction (f: abstractionMap) (g: Graph.t)
                      (transMap: (Edge.t, int) Hashtbl.t)
                      (mergeMap: (Vertex.t, int) Hashtbl.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : NodeGroups.t VertexMap.t) =
    List.fold_left (fun acc v ->
        let vhat = getGroup f v in
        let trans_pol = Hashtbl.find transMap (u,v) in
        VertexMap.update u (fun omapu ->
            match omapu with
            | None ->
               let merge_pol = Hashtbl.find mergeMap u in
               Some (merge_pol, TransferNodesSet.singleton (trans_pol, vhat))
            | Some (mp, vs) ->
               Some (mp, TransferNodesSet.add (trans_pol, vhat) vs))
                         acc) umap (neighbors g u)
  in
  (* for each node u in us, find the (abstract) nodes it's connected to and their policy *)
  let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
  AbstractNodeSet.fold (fun us f' -> split f' us) (groupKeysByValue vmap) f

let rec abstraction (f: abstractionMap) (g: Graph.t)
                    (transMap: (Edge.t, int) Hashtbl.t)
                    (mergeMap: (Vertex.t, int) Hashtbl.t) : abstractionMap =
  let f' = AbstractionMap.fold (fun _ us facc ->
               if (VertexSet.cardinal us > 1) then
                 refineAbstraction facc g transMap mergeMap us 
               else
                 facc) f f in
  if (size f = size f') then normalize f' 
  else abstraction f' g transMap mergeMap

let partialEvalTrans (network : srp) : (Edge.t, int) Hashtbl.t =
  let edge_to_val e = vtuple [vint (fst e); vint (snd e)] in
  let es = Graph.edges network.graph in
  let tbl = Hashtbl.create (List.length es) in
  List.iter (fun e ->
      let ptrans = Interp.interp_partial_closure network.trans [edge_to_val e] in
      Hashtbl.add tbl e (Syntax.hash_exp ~hash_meta:false ptrans)) es;
  tbl

let partialEvalMerge (network : srp) : (Vertex.t, int) Hashtbl.t =
  let node_to_val n = vint n in
  let ns = Graph.get_vertices network.graph in
  let tbl = Hashtbl.create (VertexSet.cardinal ns) in
  VertexSet.iter (fun v ->
      let pmerge = Interp.interp_partial_closure network.merge [node_to_val v] in
      Hashtbl.add tbl v (Syntax.hash_exp ~hash_meta:false pmerge)) ns;
  tbl

let findAbstraction (network : srp) (d: Vertex.t) : abstractionMap =
  let f = split (createAbstractionMap network.graph) (VertexSet.singleton d) in
  let transMap = partialEvalTrans network in
  let mergeMap = partialEvalMerge network in
  abstraction f network.graph transMap mergeMap

(* Many of the functions in this module have similar functionality to
   the functions above, but for failures we don't really need to care
   about the policies when computing a new abstraction as those have
   already been factored in and we are only splitting things. We just
   have to ensure a topological abstraction (forall-exists)*)
module FailuresAbstraction =
  struct
    module AbstractNodesMap : Map.S with type key := AbstractNodeSet.t = Map.Make(AbstractNodeSet)
    type splittings = Mesh | Groups of AbstractNodeSet.t

    (* given a map from concrete vertices to sets of AbstractNodes,
       reverses the mapping creating a map from AbstractNodes to set of
       concrete vertices, in effect computing sets of concrete vertices
       that map to the same AbstractNodes.*)
    let groupAbstractNodesByValue (umap: AbstractNodeSet.t VertexMap.t) : AbstractNodeSet.t =
      let reverseMap =
        VertexMap.fold (fun u vs acc ->
            AbstractNodesMap.update vs (fun us -> match us with
                                                  | None -> Some (AbstractNode.singleton u)
                                                  | Some us -> Some (AbstractNode.add u us)) acc)
                       umap AbstractNodesMap.empty in
      AbstractNodesMap.fold (fun _ v acc -> AbstractNodeSet.add v acc)
                            reverseMap AbstractNodeSet.empty  

    let refineAbstractionFailures (f: abstractionMap) (g: Graph.t)
                                  (us: AbstractNode.t) : abstractionMap =
      let refineOne (u : Vertex.t) (umap : AbstractNodeSet.t VertexMap.t) =
        List.fold_left (fun acc v ->
            let vhat = getGroup f v in
            VertexMap.update u (fun omapu ->
                               match omapu with
                               | None -> Some (AbstractNodeSet.singleton vhat)
                               | Some vs -> Some (AbstractNodeSet.add vhat vs)) acc) umap
                       (neighbors g u)
      in
      let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
      AbstractNodeSet.fold (fun us f' -> split f' us) (groupAbstractNodesByValue vmap) f

    let rec abstractionFailures (f: abstractionMap) (g: Graph.t) : abstractionMap =
      let f' = AbstractionMap.fold (fun _ us facc ->
                   if (VertexSet.cardinal us > 1) then
                     refineAbstractionFailures facc g us 
                   else
                     facc) f f in
      if (size f = size f') then normalize f' 
      else abstractionFailures f' g
      
    (* For each abstract node [uhat] and [vhat], partitions the concrete
       nodes in uhat into subsets s.t. that nodes in the same subset have
       edges to the same concrete nodes in [vhat] *)                              
    let splitForFailures (uhat : AbstractNode.t) (vhat : AbstractNode.t)
                         (g: Graph.t) : splittings = 
      let addNeighbor u =
        let neighborsOfu = neighbors g u in
        let neighborsOfUinV = List.filter (fun v -> AbstractNode.mem v vhat) neighborsOfu in
        (* Doing this, just to reuse groupAbstractNodesByValue *)
        AbstractNodeSet.singleton (AbstractNode.of_list neighborsOfUinV)
      in
      let connectivityMap = AbstractNode.fold (fun u acc ->
                                VertexMap.add u (addNeighbor u) acc) uhat VertexMap.empty in
      let us = groupAbstractNodesByValue connectivityMap in
      if ((AbstractNodeSet.cardinal us) = 1) then
        Mesh
      else
        Groups us

    (* using the abstract group id on path for efficiency reasons *)
    (* - assumes uid can be split
       - returns a random split with maximum ratio if the path was empty
       - returns a random split with ratio 1.0 if you immediately get to a full mesh.
       TODO: no need to return a ratio of 1.0, do max_int. Also avoid enforcing invariants
       with the ratio *)
    let bestSplitForFailures (g : Graph.t) (f: abstractionMap)
                             (uid: abstrId) (path: abstrId list) =
      let rec loop path current best =
        match path with
        | [] -> best
        | vid :: path ->
           let curGroup = getGroupById f current in
           match splitForFailures curGroup (getGroupById f vid) g with
           | Groups us when AbstractNodeSet.cardinal us = 2 ->
              (us, 0.0)
           | Groups us ->
              let szNew = AbstractNodeSet.cardinal us in
              let szCur = AbstractNode.cardinal curGroup in
              let ratio = (float_of_int szNew) /. (float_of_int szCur) in
              (* heuristic *)
              if (ratio < snd best) then
                loop path vid (us, ratio)
              else
                loop path vid best
           | Mesh ->
              (* do a randomSplit if necessary, but maybe there are better options*)
              if (snd best) > 1.0 then
                let u1, u2 = AbstractNode.randomSplit curGroup in
                (AbstractNodeSet.of_list [u1;u2], 1.0)
              else
                best
      in
      let u1, u2 = AbstractNode.randomSplit (getGroupById f uid) in
      loop path uid (AbstractNodeSet.of_list [u1;u2], float_of_int max_int)


    let splitSet_debug us =
      if !debugAbstraction then
        show_message (AbstractNode.printAbstractNode us) T.Blue "splitting set"
      
    (* Repeatedly split to create the abstract nodes in [uss] *)
    let splitSet f (uss : AbstractNodeSet.t) : abstractionMap =
      AbstractNodeSet.fold (fun us f' -> splitSet_debug us; split f' us) uss f

    let refineForFailures_debug (f: abstractionMap) =
      if !debugAbstraction then
        show_message (printAbstractGroups f "\n") T.Blue
                     "Abstract groups after refine for failures "
      
    let refineForFailures (g: Graph.t) (f: abstractionMap)
                          (uid: abstrId) (path: abstrId list) : abstractionMap =
      let (uss, _) = bestSplitForFailures g f uid path in
      let f' = splitSet f uss in
      let f'' =  abstractionFailures f' g in
      refineForFailures_debug f'';
      f''
      
  end
  
(* let abstractName (uhat: AbstractNode.t) : string option = *)
(*   match AbstractNode.is_empty uhat with *)
(*   | true -> None *)
(*   | false -> *)
(*      let str = "{" ^ (AbstractNode.fold (fun u acc -> (Vertex.printVertex u) ^ "," ^ acc) *)
(*                                         uhat "") in *)
(*      Some ((String.sub str 0 ((String.length str) -1)) ^ "}") *)

let addAbstractEdges (g: Graph.t) (f: abstractionMap) (ag: Graph.t)
                     (uhat: AbstractNode.t) : Graph.t =
  let repru = getGroupRepresentative f uhat in
  let ns = neighbors g repru in
  let unode = getGroupId f uhat in
  let nshat = List.map (fun v -> unode, getId f v) ns in
  add_edges ag nshat

(* Requires that abstract group ids are contiguous, hence normalizes them *)
let buildAbstractGraph (g: Graph.t) (f: abstractionMap) : Graph.t =
  let groups = getAbstractGroups f in
  let ag = Graph.create (UInt32.of_int (size f)) in
  List.fold_left (fun acc uhat -> addAbstractEdges g f acc uhat) ag groups  


let abstractToConcreteEdge (g: Graph.t) (f: abstractionMap) (ehat: Edge.t) : EdgeSet.t =
  let (uhat, vhat) = ehat in
  let us = getGroupById f uhat in (* get nodes represented by uhat *)
  let getNeighborsInVhat u =
    BatList.filter_map (fun v ->
        if (getId f v = vhat) then Some (u,v) else None) (neighbors g u)
    |> EdgeSet.of_list
  in
  AbstractNode.fold
    (fun u acc -> EdgeSet.union (getNeighborsInVhat u) acc) us EdgeSet.empty
  
let getEdgeMultiplicity (g: Graph.t) (f: abstractionMap) (ehat: Edge.t) : int =
  EdgeSet.cardinal (abstractToConcreteEdge g f ehat)
