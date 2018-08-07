open Unsigned

module Rep = Map.Make (struct
  type t = UInt32.t

  let compare = UInt32.compare
end)

type 'a t = 'a Rep.t * 'a

let less i j = UInt32.compare i j = -1

let create default : 'a t = (Rep.empty, default)

let find (m, default) k =
  match Rep.find_opt k m with None -> default | Some v -> v

let update (m, default) k v = (Rep.add k v m, default)

let map f (m, default) = (Rep.map f m, f default)

(* creates an array of length equal to the larger of the two inputs *)
(*('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t *)
let merge (f: 'a -> 'b -> 'c) ((m1, default1): 'a t) ((m2, default2): 'b t) :
    'c t =
  let default = f default1 default2 in
  let f_checked k m1v m2v =
    match (m1v, m2v) with
    | Some x, Some y -> Some (f x y)
    | Some x, None -> Some (f x default2)
    | None, Some y -> Some (f default1 y)
    | None, None -> Some default
  in
  (Rep.merge f_checked m1 m2, default)

let equal equal_vals (m1, default1) (m2, default2) =
  let test_default () = equal_vals default1 default2 in
  test_default () && Rep.equal equal_vals m1 m2

let bindings (m, default) = (Rep.bindings m, default)

let from_bindings (bs, default) =
  let m = List.fold_left (fun m (i, d) -> Rep.add i d m) Rep.empty bs in
  (m, default)
