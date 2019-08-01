open BatMap
open Unsigned

type ('k, 'v) t = ('k, 'v) PMap.t * 'v

let create cmp (default: 'v) : ('k, 'v) t = (PMap.create cmp, default)

let find (m, default) k = PMap.find_default default k m

let update (m, default) k v = (PMap.add k v m, default)

let map f (m, default) = (PMap.map f m, f default)

(* creates an array of length equal to the larger of the two inputs *)
(*('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
let merge f (m1, default1) (m2, default2) =
  let default = f default1 default2 in
  let f_checked _ m1v m2v =
    match (m1v, m2v) with
    | Some x, Some y -> Some (f x y)
    | Some x, None -> Some (f x default2)
    | None, Some y -> Some (f default1 y)
    | None, None -> Some default
  in
  (PMap.merge f_checked m1 m2, default)

let equal equal_vals (m1, default1) (m2, default2) =
  let test_default () = equal_vals default1 default2 in
  test_default () && PMap.equal equal_vals m1 m2

let bindings (m, default) = (PMap.bindings m, default)

let from_bindings cmp (bs, default) =
  let m =
    List.fold_left
      (fun m (i, d) -> PMap.add i d m)
      (PMap.create cmp) bs
  in
  (m, default)

let compare cmp (m1, d1) (m2, d2) =
  let c = PMap.compare cmp m1 m2 in
  if c <> 0 then c else cmp d1 d2
