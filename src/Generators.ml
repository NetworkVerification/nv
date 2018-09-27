open Collections
open Random
open Syntax
open Unsigned

let rec random_value ~hints ~max_map_size ty =
  let i = Random.int 10 in
  match (TypeMap.find_opt ty hints, i < 9) with
  | Some vs, true ->
      let x = Random.int (ValueSet.cardinal vs) in
      List.nth (ValueSet.elements vs) x
  | _ ->
    match get_inner_type ty with
    | TBool -> vbool (Random.bool ())
    | TInt width ->
      let x = Integer.create_64 ~value:(Random.int64 Int64.max_int) ~size:(Z.to_int width) in
        vint x
    | TTuple ts ->
        vtuple
          (List.map (fun ty -> random_value hints max_map_size ty) ts)
    | TOption ty ->
        let b = Random.bool () in
        if b then voption None
        else voption (Some (random_value hints max_map_size ty))
    | TMap (ty1, ty2) ->
        let default = random_value hints max_map_size ty2 in
        let map = ref (BddMap.create ~key_ty:ty1 default) in
        let x = Random.int max_map_size in
        for i = 1 to x do
          let k = random_value hints max_map_size ty1 in
          let v = random_value hints max_map_size ty2 in
          map := BddMap.update !map k v
        done ;
        vmap !map
    | QVar _ | TVar _ -> failwith "internal error (random_value)"
    | TArrow (ty1, ty2) -> failwith "unimplemented"

let random_symbolic hints max_map_size d =
  match d with
  | DSymbolic (x, te) ->
      let ty = match te with Ty ty -> ty | Exp e -> oget e.ety in
      let e = e_val (random_value hints max_map_size ty) in
      (* Printf.printf "Random for %s is now %s\n" (Var.to_string x)
        (Printing.exp_to_string e) ; *)
      DSymbolic (x, Exp e)
  | _ -> d

let random_symbolics ?hints ?max_map_size ds =
  let hints =
    match hints with None -> TypeMap.empty | Some hs -> hs
  in
  let sz = match max_map_size with None -> 3 | Some x -> x in
  List.map (random_symbolic hints sz) ds
