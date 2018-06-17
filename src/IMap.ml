open Unsigned
  
module Rep =
  Map.Make (
    struct
      type t = UInt32.t
      let compare = UInt32.compare
    end
  )
      
type 'a t = 'a Rep.t * UInt32.t

let less i j = UInt32.compare i j = -1
let in_bounds i length  = less i length && not (less i UInt32.zero)
      
let create l = (Rep.empty, l)
    
let get (m,l) k =
  if not(in_bounds k l) then
    None
  else
    Rep.find_opt k m
	
let set (m,l) k v =
  if not(in_bounds k l) then
    (m,l)
  else
    (Rep.add k v m, l)
      
let map f (m,l) =
  (Rep.map f m, l)

(* creates an array of length equal to the smaller of the two inputs *)
let merge f (m1,i1) (m2,i2) =
  let length = if i1 < i2 then i1 else i2 in
  (Rep.merge (fun k m1v m2v ->
    if not (in_bounds k length) then
      None
    else
      f m1v m2v) m1 m2, length)
      
let equal equal_vals (m1,i1) (m2,i2) =
  (UInt32.compare i1 i2 = 0) && (Rep.equal equal_vals m1 m2)

let length (m,i) = i
  
let bindings (m,i) = Rep.bindings m
