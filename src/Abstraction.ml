open Graph
open AbstractionMap
open Unsigned
open Console

module AbstractNodeSet : Set.S with type elt := AbstractNode.t = Set.Make(AbstractNode)
module AbstractNodesMap : Map.S with type key := AbstractNodeSet.t = Map.Make(AbstractNodeSet)

let debugAbstraction = ref true
                                                                   
let groupKeysByValue (umap: AbstractNodeSet.t VertexMap.t) : AbstractNodeSet.t =
  let reverseMap =
    VertexMap.fold (fun u vs acc ->
        AbstractNodesMap.update vs (fun us -> match us with
                                              | None -> Some (AbstractNode.singleton u)
                                              | Some us -> Some (AbstractNode.add u us)) acc)
                   umap AbstractNodesMap.empty in
  AbstractNodesMap.fold (fun _ v acc -> AbstractNodeSet.add v acc)
                        reverseMap AbstractNodeSet.empty  
                                                                   
let refineAbstraction (g: Graph.t) (f: abstractionMap) (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : AbstractNodeSet.t VertexMap.t) =
    List.fold_left (fun acc v ->
        let vhat = getGroup f v in
        VertexMap.update u (fun omapu ->
            match omapu with
            | None -> Some (AbstractNodeSet.singleton vhat)
            | Some vs -> Some (AbstractNodeSet.add vhat vs)) acc) umap (neighbors g u)
  in
  let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
  AbstractNodeSet.fold (fun us f' -> split f' us) (groupKeysByValue vmap) f

let rec abstraction (f: abstractionMap) (g: Graph.t) =
  let f' = fold (fun _ us facc ->
               if (VertexSet.cardinal us > 1) then
                 refineAbstraction g facc us
               else
                 facc) f f in
  if (size f = size f') then normalize f' 
  else abstraction f' g
  
let findAbstraction (g : Graph.t) (d: Vertex.t) : abstractionMap =
  let f = split (createAbstractionMap g) (VertexSet.singleton d) in
  abstraction f g

type splittings = Mesh | Groups of AbstractNodeSet.t
                                 
let splitForFailures (uhat : AbstractNode.t) (vhat : AbstractNode.t) g = 
  let addNeighbor u =
    let neighborsOfu = neighbors g u in
    let neighborsOfUinV = List.filter (fun v -> AbstractNode.mem v vhat) neighborsOfu in
    AbstractNodeSet.singleton (AbstractNode.of_list neighborsOfUinV)
                              (* Doing this, just to reuse groupKeysByValues, for now*)
  in
  let conMap = AbstractNode.fold (fun u acc ->
                   VertexMap.add u (addNeighbor u) acc) uhat VertexMap.empty in
  let us = groupKeysByValue conMap in
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
let bestSplitForFailures (g : Graph.t) (f: abstractionMap) (uid: abstrId) (path: abstrId list) =
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
  
(* TODO: Refine for failures does not need to take the transfer
   function into consideration when refining hence using the same
   function as findAbstraction is not the best for
   efficiency. Optimize that when we add reasoning about transfer
   functions *)
let refineForFailures (g: Graph.t) (f: abstractionMap)
                      (uid: abstrId) (path: abstrId list) : abstractionMap =
  match bestSplitForFailures g f uid path with
  | (uss, _) ->
     let f' = splitSet f uss in
     let f'' =  abstraction f' g in
     refineForFailures_debug f'';
     f''

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
