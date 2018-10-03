open Graph
open Unsigned
open Vertex
   
module AbstractNode =
  struct
    include VertexSet
    let printAbstractNode (us : t) =
      let rec printAux lst acc =
        match lst with
        | [] -> "}" :: acc
        | [u] -> printAux [] ((Printf.sprintf "%s" (printVertex u)) :: acc)
        | u :: lst -> printAux lst ((Printf.sprintf "%s," (printVertex u)) :: acc)
      in
      String.concat "" (List.rev (printAux (elements us) ["{"]))

    let randomSplit (us : t) : (t * t) =
      let u1, u2, _ =
        fold (fun u (s1,s2,b) ->
            if b then
              (add u s1, s2, false)
            else
              (s1, add u s2, true)) us (empty, empty, true)
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
  VertexMap.find_opt u (f.groupId)

let getGroupById (f: abstractionMap) (idx: abstrId) : AbstractNode.t =
  GroupMap.find idx (f.absGroups)

let getGroup (f: abstractionMap) (u: Vertex.t) : AbstractNode.t =
  getGroupById f (getId f u)

let getGroupRepresentative (f: abstractionMap) (u: AbstractNode.t) : Vertex.t =
  AbstractNode.min_elt u

let getGroupRepresentativeId (f: abstractionMap) (uhat: abstrId) : Vertex.t =
  getGroupRepresentative f (getGroupById f uhat)
  
let getGroupId (f: abstractionMap) (u: AbstractNode.t) : abstrId =
  getId f (getGroupRepresentative f u)

(* Removes the node u from it's current abstract group and assigns it to the id newId *)
let partitionNode (f: abstractionMap) (newId: abstrId) (u: Vertex.t) : unit =
  let _ =  match getIdPartial f u with
    | Some idx ->
       let us = getGroupById f idx in
       let newUs = AbstractNode.remove u us in
       if AbstractNode.is_empty newUs then
         f.absGroups <- GroupMap.remove idx (f.absGroups)
       else
         f.absGroups <- GroupMap.add idx newUs (f.absGroups)
    | None -> ()
  in
  f.groupId <- VertexMap.add u newId (f.groupId)

(* Removes the nodes us from their current abstract group and adds
   them to a new abstract group designated by identifier i*)
let partitionNodes (f: abstractionMap) (i: abstrId) (us: AbstractNode.t) : unit =
  AbstractNode.iter (fun u -> partitionNode f i u) us;
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

let fold (g: Vertex.t -> AbstractNode.t -> 'a -> 'a) (f: abstractionMap) (acc: 'a) : 'a =
  VertexMap.fold (fun u idx acc -> g u (getGroupById f idx) acc) f.groupId acc

let size (f: abstractionMap) : int =
  VertexMap.cardinal f.groupId

let normalize (f: abstractionMap) =
  let (nextIdN, groupIdN, absGroupsN) =
    GroupMap.fold (fun id us (nextIdN, groupIdN, absGroupsN) ->
        (UInt32.add nextIdN UInt32.one,
         AbstractNode.fold (fun u acc -> VertexMap.add u nextIdN acc) us groupIdN,
         GroupMap.add nextIdN (getGroupById f id) absGroupsN))
                   f.absGroups (UInt32.zero, VertexMap.empty, GroupMap.empty)
  in
  { absGroups = absGroupsN; groupId = groupIdN; nextId = nextIdN}
    
