type t = {size: Z.t; value: Z.t}

let of_string (s : string) : t =
  let lst = List.map Z.of_string @@ Str.split (Str.regexp "u") s in
  match lst with
  | [] -> failwith "This is literally impossible"
  | value::[] -> {size = Z.of_int 32; value}
  | value::size::[] -> {size; value}
  | _ -> failwith "Integer.of_string: Too many values"
;;

let of_int (n : int) : t =
  {size = Z.of_int 32; value = Z.of_int n}

let of_size_and_val (value : int) (size : int) : t =
  {size = Z.of_int size; value = Z.of_int value}

let check x y =
  if not (Z.equal x.size y.size) then
    failwith "integer bit sizes did not match"

let modulo = Big_int_Z.mod_big_int

let size x = x.size

let add x y =
  check x y ;
  let value = modulo (Z.add x.value y.value) x.size in
  {size= x.size; value}

let sub x y =
  check x y ;
  let value = modulo (Z.sub x.value y.value) x.size in
  {size= x.size; value}

let create sz str =
  let size = Z.of_int sz in
  let value = Z.of_string str in
  {size; value}

let lt x y = check x y ; Z.lt x.value y.value

let leq x y = check x y ; Z.leq x.value y.value

let gt x y = check x y ; Z.gt x.value y.value

let geq x y = check x y ; Z.geq x.value y.value
