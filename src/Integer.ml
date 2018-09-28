type t = {size: Z.t; value: Z.t}

let modulo = Big_int_Z.mod_big_int

let mod_by_size (x : t) : t =
  {size = x.size; value = modulo x.value x.size}

let of_string (s : string) : t =
  let lst = List.map Z.of_string @@ Str.split (Str.regexp "u") s in
  match lst with
  | [] -> failwith "Integer.of_string: This is literally impossible"
  | value::[] -> mod_by_size {size = Z.of_int 32; value}
  | value::size::[] -> mod_by_size {size; value}
  | _ -> failwith "Integer.of_string: Too many values"
;;

let of_int (n : int) : t =
  mod_by_size {size = Z.of_int 32; value = Z.of_int n}

let create ~(value : int) ~(size : int) : t =
  mod_by_size {size = Z.of_int size; value = Z.of_int value}

let create_64 ~(value : Int64.t) ~(size : int) : t =
  mod_by_size {size = Z.of_int size; value = Z.of_int64 value}

let check x y =
  if not (Z.equal x.size y.size) then
    failwith "integer bit sizes did not match"

let size x = Z.to_int x.size

let value x = x.value

let to_int x = Z.to_int x.value

let to_string x = (Z.to_string x.value) ^ "u" ^ (Z.to_string x.size)

let add x y =
  check x y ;
  let value = modulo (Z.add x.value y.value) x.size in
  {size= x.size; value}

let sub x y =
  check x y ;
  let value = modulo (Z.sub x.value y.value) x.size in
  {size= x.size; value}

let shift_left (x : t) (n : int) =
  let value = modulo (Z.shift_left x.value n) x.size in
  {size= x.size; value}

let pred x =
  let value = modulo (Z.sub x.value Z.one) x.size in
  {size = x.size; value}

let succ x =
  let value = modulo (Z.add x.value Z.one) x.size in
  {size = x.size; value}

let lt x y = check x y ; Z.lt x.value y.value

let leq x y = check x y ; Z.leq x.value y.value

let gt x y = check x y ; Z.gt x.value y.value

let geq x y = check x y ; Z.geq x.value y.value

let equal x y = (x.size = y.size) && (x.value = y.value)

let compare x y = check x y; Z.compare x.value y.value
