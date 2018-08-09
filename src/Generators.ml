open Random
open Syntax
open Unsigned

(* TODO: add a hints option to bias for constants that appear in the program *)

let rec default_value ty =
  let v =
    match ty with
    | TBool -> VBool false
    | TInt _ -> VUInt32 (UInt32.of_int 0)
    | TTuple ts -> VTuple (List.map default_value ts)
    | TOption ty -> VOption None
    | TMap (ty1, ty2) -> VMap (IMap.create compare_values (default_value ty2))
    | TVar _ | QVar _ | TArrow _ ->
        Console.error "internal error (default_value)"
  in
  value v

let rec random_value ?max_map_size ty =
  match Typing.get_inner_type ty with
  | TBool -> VBool (Random.bool ()) |> value
  | TInt _ ->
      let x = UInt32.of_int64 (Random.int64 Int64.max_int) in
      VUInt32 x |> value
  | TTuple ts ->
      VTuple (List.map (fun ty -> random_value ?max_map_size ty) ts) |> value
  | TOption ty ->
      let b = Random.bool () in
      if b then VOption None |> value
      else VOption (Some (random_value ?max_map_size ty)) |> value
  | TMap (ty1, ty2) ->
      let default = random_value ?max_map_size ty2 in
      let map = ref (IMap.create compare_values default) in
      let sz = match max_map_size with None -> 3 | Some x -> x in
      let x = Random.int sz in
      for i = 1 to x do
        let k = random_value ?max_map_size ty1 in
        let v = random_value ?max_map_size ty2 in
        map := IMap.update !map k v
      done ;
      VMap !map |> value
  | QVar _ | TVar _ -> Console.error "internal error (random_value)"
  | TArrow (ty1, ty2) -> Console.error "unimplemented"

let random_symbolic ?max_map_size d =
  match d with
  | DSymbolic (x, te) ->
      let ty = match te with Ty ty -> ty | Exp e -> oget e.ety in
      let e = EVal (random_value ?max_map_size ty) |> exp in
      DSymbolic (x, Exp e)
  | _ -> d

let random_symbolics ?max_map_size ds =
  List.map (random_symbolic ?max_map_size) ds
