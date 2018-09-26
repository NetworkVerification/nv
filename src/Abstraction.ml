open Graph
open AbstractionMap
open Unsigned
open Console
open Srp
open Hashtbl
open Syntax
open BatSet

let debugAbstraction = ref true

(** Sets of Abstract Nodes *)
module AbstractNodeSet : Set.S with type elt := AbstractNode.t = Set.Make(AbstractNode)

(** Sets of Abstract Node Ids *)
type absIdSet = abstrId BatSet.t

(** transfer hash, abstract id *)
type transAbsId = int * abstrId

(** merge_hash * {(trans_hash, abstractId)}*) 
type policyAbsId = int * (transAbsId BatSet.t)
                                                               
(** Given a map from vertices to elements of type 'a, returns the sets
   of vertices that map to the same elements.  *)     
let groupKeysByValue (umap: 'a VertexMap.t) : AbstractNodeSet.t =
  let reverseMap : ('a, AbstractNode.t) BatMap.t =
    VertexMap.fold (fun u vhat acc ->
        BatMap.modify_opt vhat (fun us -> match us with
                                              | None -> Some (AbstractNode.singleton u)
                                              | Some us -> Some (AbstractNode.add u us)) acc)
                   umap BatMap.empty in
  BatMap.fold (fun v acc -> AbstractNodeSet.add v acc)
                      reverseMap AbstractNodeSet.empty
  
(* This does not handle a forall-forall abstraction. *)  
let refineTopological (f: abstractionMap) (g: Graph.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : absIdSet VertexMap.t) =
    List.fold_left (fun acc v ->
        let vhat = getId f v in
        VertexMap.update u (fun omapu ->
                           match omapu with
                           | None -> Some (BatSet.singleton vhat)
                           | Some vs -> Some (BatSet.add vhat vs)) acc) umap
                   (neighbors g u)
  in
  let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
  AbstractNodeSet.fold (fun us f' -> AbstractionMap.split f' us) (groupKeysByValue vmap) f

let rec abstractionTopological (f: abstractionMap) (g: Graph.t) : abstractionMap =
  let f' = AbstractionMap.fold (fun _ us facc ->
               if (VertexSet.cardinal us > 1) then
                 refineTopological facc g us 
               else
                 facc) f f in
  if (size f = size f') then normalize f' 
  else abstractionTopological f' g
 
let refineAbstraction (f: abstractionMap) (g: Graph.t)
                      (transMap: (Edge.t, int) Hashtbl.t)
                      (mergeMap: (Vertex.t, int) Hashtbl.t)
                      (us: AbstractNode.t) : abstractionMap =
  let refineOne (u : Vertex.t) (umap : policyAbsId VertexMap.t) =
    List.fold_left (fun acc v ->
        let vhat = getId f v in
        let trans_pol = Hashtbl.find transMap (u,v) in
        VertexMap.update u (fun omapu ->
            match omapu with
            | None ->
               let merge_pol = Hashtbl.find mergeMap u in
               Some (merge_pol, BatSet.singleton (trans_pol, vhat))
            | Some (mp, vs) ->
               Some (mp, BatSet.add (trans_pol, vhat) vs))
                         acc) umap (neighbors g u)
  in
  (* for each node u in us, find the (abstract) nodes it's connected to and their policy *)
  let vmap = AbstractNode.fold (fun u acc -> refineOne u acc) us VertexMap.empty in
  AbstractNodeSet.fold (fun us f' -> AbstractionMap.split f' us) (groupKeysByValue vmap) f

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
      (* remove unused variables from closures before hashing transfer functions *)
      Printf.printf "%s\n"
                    (Syntax.show_exp ~show_meta:false
                                        (exp_of_value (vclosure (network.trans))));
      let ptrans = free_dead_vars
                     (Interp.interp_partial_closure network.trans [edge_to_val e]) in
      Printf.printf "edge (%d,%d): %s\n" (UInt32.to_int (fst e)) (UInt32.to_int (snd e))
      (Syntax.show_exp ~show_meta:false ptrans);
      Hashtbl.add tbl e (Syntax.hash_exp ~hash_meta:false ptrans)) es;
  tbl

let partialEvalMerge (network : srp) : (Vertex.t, int) Hashtbl.t =
  let node_to_val n = vint n in
  let ns = Graph.get_vertices network.graph in
  let tbl = Hashtbl.create (VertexSet.cardinal ns) in
  VertexSet.iter (fun v ->
      let pmerge = free_dead_vars
                     (Interp.interp_partial_closure network.merge [node_to_val v]) in
      Hashtbl.add tbl v (Syntax.hash_exp ~hash_meta:false pmerge)) ns;
  tbl

let findAbstraction (network : srp) (d: Vertex.t) : abstractionMap =
  let f = AbstractionMap.split (createAbstractionMap network.graph) (VertexSet.singleton d) in
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
    type splittings = Mesh | Groups of AbstractNodeSet.t

    (* For each abstract node [uhat] and [vhat], partitions the concrete
       nodes in uhat into subsets s.t. that nodes in the same subset have
       edges to the same concrete nodes in [vhat] *)                              
    let splitForFailures (uhat : AbstractNode.t) (vhat : AbstractNode.t)
                         (g: Graph.t) : splittings = 
      let addNeighbor u =
        let neighborsOfu = neighbors g u in
        let neighborsOfUinV = List.filter (fun v -> AbstractNode.mem v vhat) neighborsOfu in
        AbstractNode.of_list neighborsOfUinV
      in
      let connectivityMap = AbstractNode.fold (fun u acc ->
                                VertexMap.add u (addNeighbor u) acc) uhat VertexMap.empty in
      let us = groupKeysByValue connectivityMap in
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
      AbstractNodeSet.fold
        (fun us f' -> splitSet_debug us; AbstractionMap.split f' us) uss f

    let refineForFailures_debug (f: abstractionMap) =
      if !debugAbstraction then
        show_message (printAbstractGroups f "\n") T.Blue
                     "Abstract groups after refine for failures "
      
    let refineForFailures (g: Graph.t) (f: abstractionMap)
                          (uid: abstrId) (path: abstrId list) : abstractionMap =
      let (uss, _) = bestSplitForFailures g f uid path in
      let f' = splitSet f uss in
      let f'' =  abstractionTopological f' g in
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
