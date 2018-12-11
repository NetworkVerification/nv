open AdjGraph
open Unsigned
open Vertex
   
module AbstractNode =
  struct
    include AdjGraph.VertexSet

    let toSet x = x
    let fromSet x = x
                  
    let printAbstractNode (us : t) =
      let rec printAux lst acc =
        match lst with
        | [] -> "}" :: acc
        | [u] -> printAux [] ((Printf.sprintf "%s" (printVertex u)) :: acc)
        | u :: lst -> printAux lst ((Printf.sprintf "%s," (printVertex u)) :: acc)
      in
      String.concat "" (List.rev (printAux (VertexSet.elements us) ["{"]))

    let randomSplit (us : t) : (t * t) =
      let u1, u2, _ =
        VertexSet.fold (fun u (s1,s2,b) ->
            if b then
              (VertexSet.add u s1, s2, false)
            else
              (s1, VertexSet.add u s2, true)) us (VertexSet.empty, VertexSet.empty, true)
      in
      (u1, u2)
  end

module UInts = struct
  type t = Integer.t

  let compare = Integer.compare
end

type abstrId = UInts.t
module GroupMap = BatMap.Make(UInts)


(* when doing this in a functional style, it hangs. I am pretty sure,
   I created an infinite loop, I can't imagine the performance being
   so horrible *)
type abstractionMap =
  { absGroups : AbstractNode.t GroupMap.t; (* mapping each id to a set of nodes *)
    groupId   : abstrId VertexMap.t;       (* mapping each node to an id *)
    nextId    : abstrId;                   (* next available id *)
  }

let getId (f: abstractionMap) (u: Vertex.t) : abstrId =
  VertexMap.find u (f.groupId)

let getIdPartial (f: abstractionMap) (u: Vertex.t) : abstrId option =
  VertexMap.Exceptionless.find u (f.groupId)

let getGroupById (f: abstractionMap) (idx: abstrId) : AbstractNode.t =
  GroupMap.find idx (f.absGroups)

let getGroup (f: abstractionMap) (u: Vertex.t) : AbstractNode.t =
  getGroupById f (getId f u)

let getGroupRepresentative (f: abstractionMap) (u: AbstractNode.t) : Vertex.t =
  VertexSet.min_elt u

let getGroupRepresentativeId (f: abstractionMap) (uhat: abstrId) : Vertex.t =
  getGroupRepresentative f (getGroupById f uhat)
  
let getGroupId (f: abstractionMap) (u: AbstractNode.t) : abstrId =
  getId f (getGroupRepresentative f u)
  
(* Removes the node u from it's current abstract group and assigns it to the id newId *)
let partitionNode (f: abstractionMap) (newId: abstrId) (u: Vertex.t) : abstractionMap =
  let f' =  match getIdPartial f u with
    | Some idx ->
       let us = getGroupById f idx in
       let newUs = VertexSet.remove u us in
       if VertexSet.is_empty newUs then
         {f with absGroups = GroupMap.remove idx (f.absGroups)}
       else
         {f with absGroups = GroupMap.add idx newUs (f.absGroups)}
    | None -> f
  in
  {f' with groupId = VertexMap.add u newId (f'.groupId)}

(* Removes the nodes us from their current abstract group and adds
   them to a new abstract group designated by identifier i*)
let partitionNodes (f: abstractionMap) (i: abstrId) (us: AbstractNode.t) : abstractionMap =
  let f' = VertexSet.fold (fun u f' -> partitionNode f' i u) us f in
  {f' with absGroups = GroupMap.add i us (f'.absGroups)}

let split (f: abstractionMap) (us: AbstractNode.t) : abstractionMap =
  let f' = {absGroups = f.absGroups;
            groupId = f.groupId;
            nextId = Integer.succ f.nextId} in
  partitionNodes f' (f'.nextId) us

let getAbstractGroups (f: abstractionMap) : (GroupMap.key * AbstractNode.t) list =
  GroupMap.bindings f.absGroups

let printAbstractGroups (f: abstractionMap) (sep: string) : string =
  List.fold_left (fun acc (k, us) ->
      (Integer.to_string k) ^ ": " ^
        (AbstractNode.printAbstractNode us) ^ sep ^ acc)
    "" (getAbstractGroups f)

let createAbstractionMap g : abstractionMap =
  let f = { absGroups = GroupMap.empty;
            groupId = VertexMap.empty;
            nextId = Integer.create ~value:0 ~size:32} in
  partitionNodes f (f.nextId) (AdjGraph.get_vertices g)

let fold (g: AbstractNode.t -> 'a -> 'a) (f: abstractionMap) (acc: 'a) : 'a =
  GroupMap.fold (fun idx us acc -> g us acc) f.absGroups acc

let size (f: abstractionMap) : int =
  GroupMap.cardinal (f.absGroups)
(* f.nextId |> UInt32.to_int *)

let copyMap (f: abstractionMap) =
  {absGroups = f.absGroups; groupId = f.groupId; nextId = f.nextId}

(* does not preserve ids through refinements *)
let normalize (f: abstractionMap) =
  let init =  (Integer.create ~value:0 ~size:32, VertexMap.empty, GroupMap.empty) in
  let (nextIdN, groupIdN, absGroupsN) =
    GroupMap.fold (fun id us (nextIdN, groupIdN, absGroupsN) ->
        (Integer.succ nextIdN,
         VertexSet.fold (fun u acc -> VertexMap.add u nextIdN acc) us groupIdN,
         GroupMap.add nextIdN (getGroupById f id) absGroupsN))
                  f.absGroups init
  in
  { absGroups = absGroupsN; groupId = groupIdN; nextId = nextIdN}

(* let normalize (fprev: abstractionMap) (f: abstractionMap) =
 *   let init = ([], VertexMap.empty, GroupMap.empty) in
 *   Printf.printf "in normalize fprev: %s" (printAbstractGroups fprev "\n");
 *   Printf.printf "in normalize f: %s" (printAbstractGroups f "\n");
 *   (\* insert into the new abstractionmap the nodes that existed in the
 *      previous one with the same id as before *\)
 *   let (leftovers, groupIdN, absGroupsN) =
 *     GroupMap.fold (fun id us (leftovers, groupIdN, absGroupsN) ->
 *         let repr = getGroupRepresentative f us in
 *         let oldid = getId fprev repr in
 *         if not (GroupMap.mem oldid absGroupsN) then
 *           begin
 *             Printf.printf "enter for oldid:%d\n" (Integer.to_int oldid);
 *           (leftovers,
 *            VertexSet.fold (fun u acc -> VertexMap.add u oldid acc) us groupIdN,
 *            GroupMap.add oldid us absGroupsN)
 *           end
 *         else
 *           begin
 *               Printf.printf "else for oldid:%d\n" (Integer.to_int oldid);
 *               ((id,us) :: leftovers, groupIdN, absGroupsN)
 *             end
 *       )
 *       f.absGroups init in
 *   (\* any node that has an id >= sz should be inserted with a new fresh
 *      id s.t. new_id < sz*\)
 *   (\*todo fix this second part *\)
 *   let (nextIdN, groupIdN, absGroupsN) =
 *     List.fold_left (fun (nextIdN, groupIdN, absGroupsN) (id, us) ->
 *         let freshId = ref nextIdN in
 *         while GroupMap.mem !freshId absGroupsN do
 *           freshId := Integer.succ !freshId;
 *         done;
 *         (Integer.succ !freshId,
 *          VertexSet.fold (fun u acc -> VertexMap.add u !freshId acc) us groupIdN,
 *          GroupMap.add !freshId us absGroupsN))
 *                    (Integer.create ~value:0 ~size:32, groupIdN, absGroupsN) leftovers
 *   in { absGroups = absGroupsN; groupId = groupIdN; nextId = nextIdN} *)

    
