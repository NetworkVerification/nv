module M = Map.Make (Var)

exception EError of string

let error s = raise (EError s)

type 'a t = 'a M.t

let empty = M.empty

exception Unbound_var of Var.t

let lookup env x = try M.find x env with Not_found -> raise (Unbound_var x)

let update env x entry = M.add x entry env

(* update env1 with the bindings of env2.  If both environments have the same key, env2 shadows env1 *)
let updates env1 env2 = M.union (fun k v1 v2 -> Some v2) env1 env2

let bind x entry = M.add x entry empty

let to_string entry_to_string env =
  M.fold
    (fun k v s -> Var.to_string k ^ "=" ^ entry_to_string v ^ ";" ^ s)
    env ""


let to_list env = M.bindings env
