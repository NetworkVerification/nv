type t = string * int [@@deriving show]

let counter = ref 0

let next () =
  counter := !counter + 1 ;
  !counter

let reset () = counter := 0

let fresh s = (s, next ())

let create s = (s, 0)

let name (s, i) = s

let to_var (s, i) = (s, i)

let from_var (s, i) = (s, i)

let to_string (s, i) = s ^ string_of_int i

let equals (s1, i1) (s2, i2) = s1 = s2 && i1 = i2

let equal_names (s1, i1) (s2, i2) = s1 = s2

let compare (s1, i1) (s2, i2) =
  if s1 < s2 then -1
  else if s1 > s2 then 1
  else if i1 < i2 then -1
  else if i1 > i2 then 1
  else 0
