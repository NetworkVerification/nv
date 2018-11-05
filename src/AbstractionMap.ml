open Graph
open Unsigned
open Vertex
   
module AbstractNode =
  struct
    include Graph.VertexSet

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
  type t = UInt32.t

  let compare = UInt32.compare
end

module GroupMap = Map.Make(UInts)
type abstrId = UInts.t

type abstractionMap =
  { mutable absGroups : AbstractNode.t GroupMap.t; (* mapping each id to a set of nodes *)
    mutable groupId   : abstrId VertexMap.t;       (* mapping each node to an id *)
    mutable nextId    : abstrId;                   (* next available id *)
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
let partitionNode (f: abstractionMap) (newId: abstrId) (u: Vertex.t) : unit =
  let _ =  match getIdPartial f u with
    | Some idx ->
       let us = getGroupById f idx in
       let newUs = VertexSet.remove u us in
       if VertexSet.is_empty newUs then
         f.absGroups <- GroupMap.remove idx (f.absGroups)
       else
         f.absGroups <- GroupMap.add idx newUs (f.absGroups)
    | None -> ()
  in
  f.groupId <- VertexMap.add u newId (f.groupId)

(* Removes the nodes us from their current abstract group and adds
   them to a new abstract group designated by identifier i*)
let partitionNodes (f: abstractionMap) (i: abstrId) (us: AbstractNode.t) : unit =
  VertexSet.iter (fun u -> partitionNode f i u) us;
  f.absGroups <- GroupMap.add i us (f.absGroups)

let split (f: abstractionMap) (us: AbstractNode.t) : abstractionMap =
  let f' = {absGroups = f.absGroups;
            groupId = f.groupId;
            nextId = UInt32.add f.nextId UInt32.one} in
  partitionNodes f' (f'.nextId) us;
  f'

let getAbstractGroups (f: abstractionMap) : AbstractNode.t list =
  List.map (fun (k,v) -> v) (GroupMap.bindings f.absGroups)

let printAbstractGroups (f: abstractionMap) (sep: string) : string =
  List.fold_left (fun acc us -> (AbstractNode.printAbstractNode us) ^ sep ^ acc)
                 "" (getAbstractGroups f)


let createAbstractionMap g : abstractionMap =
  let f = { absGroups = GroupMap.empty; groupId = VertexMap.empty; nextId = UInt32.zero} in
  partitionNodes f (f.nextId) (Graph.get_vertices g);
  f

let fold (g: AbstractNode.t -> 'a -> 'a) (f: abstractionMap) (acc: 'a) : 'a =
  GroupMap.fold (fun idx us acc -> g us acc) f.absGroups acc

let size (f: abstractionMap) : int =
  GroupMap.cardinal (f.absGroups)
  (* f.nextId |> UInt32.to_int *)

let normalize (f: abstractionMap) =
  let (nextIdN, groupIdN, absGroupsN) =
    GroupMap.fold (fun id us (nextIdN, groupIdN, absGroupsN) ->
        (UInt32.add nextIdN UInt32.one,
         VertexSet.fold (fun u acc -> VertexMap.add u nextIdN acc) us groupIdN,
         GroupMap.add nextIdN (getGroupById f id) absGroupsN))
                   f.absGroups (UInt32.zero, VertexMap.empty, GroupMap.empty)
  in
  { absGroups = absGroupsN; groupId = groupIdN; nextId = nextIdN}
    
