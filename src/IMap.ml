open Unsigned

module Rep = Map.Make (struct
  type t = UInt32.t

  let compare = UInt32.compare
end)

type 'a t = 'a Rep.t * 'a * UInt32.t

let less i j = UInt32.compare i j = -1

exception Out_of_bounds of UInt32.t

let in_bounds i length = less i length && not (less i UInt32.zero)

let create l default = (Rep.empty, default, l)

let find (m, default, l) k =
  if not (in_bounds k l) then raise (Out_of_bounds k)
  else match Rep.find_opt k m with None -> default | Some v -> v


let update (m, default, l) k v =
  if not (in_bounds k l) then (m, default, l) else (Rep.add k v m, default, l)


let map f (m, default, l) = (Rep.map f m, f default, l)

(* creates an array of length equal to the larger of the two inputs *)
let merge f (m1, default1, i1) (m2, default2, i2) =
  let length = if i1 > i2 then i1 else i2 in
  let f_checked k m1v m2v =
    if not (in_bounds k length) then
      failwith ("illegal key in map: " ^ UInt32.to_string k)
    else f m1v m2v
  in
  let default =
    match f (Some default1) (Some default2) with
    | Some v -> v
    | None -> failwith "bad merge function resulted in no default value"
  in
  (Rep.merge f_checked m1 m2, default, length)


let equal equal_vals (m1, default1, i1) (m2, default2, i2) =
  let test_default () =
    if UInt32.compare (UInt32.of_int (Rep.cardinal m1)) i1 = 0 then true
    else equal_vals default1 default2
  in
  UInt32.compare i1 i2 = 0 && test_default () && Rep.equal equal_vals m1 m2

let length (m, default, i) = i

let bindings (m, default, i) = (Rep.bindings m, default)

let from_bindings i (bs, default) =
  let m = List.fold_left (fun m (i,d) -> Rep.add i d m) Rep.empty bs in
  (m, default, i)
