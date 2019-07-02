type t = string * int [@@deriving show]

(* Should be a character which the NV parser doesn't allow in identifiers *)
let delim = "~"

let counter = ref 0

let next () =
  counter := !counter + 1 ;
  !counter

let reset () = counter := 0

let fresh s = (s, next ())

let create s = (s, 0)

let name (s, _i) = s

let to_var (s, i) = (s, i)

let from_var (s, i) = (s, i)

let to_string (s, i) = s ^ delim ^ string_of_int i

let of_var_string s =
  try
    let v, i = BatString.rsplit s ~by:"~" in
    (v, int_of_string i)
  with
  | _ ->
    failwith @@ Printf.sprintf "of_var_string: %s has wrong format" s

let equal (s1, i1) (s2, i2) = s1 = s2 && i1 = i2

let equals = equal

let equal_names (s1, _i1) (s2, _i2) = s1 = s2

let compare (s1, i1) (s2, i2) =
  if s1 < s2 then -1
  else if s1 > s2 then 1
  else if i1 < i2 then -1
  else if i1 > i2 then 1
  else 0
