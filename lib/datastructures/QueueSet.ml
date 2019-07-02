open BatSet

(* Purely functional queue that does not permit duplicates *)

type 'a queue =
  | Queue of ('a -> 'a -> int) * 'a list * 'a list * 'a PSet.t

let empty cmp = Queue (cmp, [], [], PSet.create cmp)

let add q elt =
  match q with Queue (cmp, front, back, set) ->
    if PSet.mem elt set then q
    else Queue (cmp, elt :: front, back, PSet.add elt set)

let add_all q es = List.fold_left (fun q e -> add q e) q es

let pop q =
  match q with
  | Queue (_, [], [], _) -> None
  | Queue (cmp, front, b :: bs, set) ->
      Some (b, Queue (cmp, front, bs, PSet.remove b set))
  | Queue (cmp, front, [], set) ->
      let back = List.rev front in
      let elt = List.hd back in
      Some (elt, Queue (cmp, [], List.tl back, PSet.remove elt set))

let iter f q =
  match q with Queue (_, front, back, _) ->
    List.iter f back ;
    List.iter f (List.rev front)
