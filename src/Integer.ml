type t = {size: Z.t; value: Z.t}

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
