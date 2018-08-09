open Random
open Syntax
open Unsigned

(* TODO: add a hints option to bias for constants that appear in the program *)

let rec random_value ty max_map_size =
  match Typing.get_inner_type ty with
  | TBool -> VBool (Random.bool ()) |> value
  | TInt _ ->
      let x = UInt32.of_int64 (Random.int64 Int64.max_int) in
      VUInt32 x |> value
  | TTuple ts ->
      VTuple (List.map (fun ty -> random_value ty max_map_size) ts) |> value
  | TOption ty ->
      let b = Random.bool () in
      if b then VOption None |> value
      else VOption (Some (random_value ty max_map_size)) |> value
  | TMap (ty1, ty2) ->
      let default = random_value ty2 max_map_size in
      let map = ref (IMap.create compare_values default) in
      let x = Random.int max_map_size in
      for i = 1 to x do
        let k = random_value ty1 max_map_size in
        let v = random_value ty2 max_map_size in
        map := IMap.update !map k v
      done ;
      VMap !map |> value
  | QVar _ | TVar _ -> Console.error "internal error (random_value)"
  | TArrow (ty1, ty2) -> Console.error "unimplemented"

let random_symbolic map_size d =
  match d with
  | DSymbolic (x, te) ->
      let ty = match te with Ty ty -> ty | Exp e -> oget e.ety in
      let e = EVal (random_value ty map_size) |> exp in
      DSymbolic (x, Exp e)
  | _ -> d

let random_symbolics ds map_size = List.map (random_symbolic map_size) ds

let check_assertions (sol: Solution.t) =
  match sol.assertions with
  | None -> true
  | Some ass -> Graph.VertexMap.for_all (fun _ b -> b) ass

let rec check_aux ds iters num_rejected acc =
  match (iters, acc) with
  | 0, _ | _, Some _ -> acc
  | _ ->
      let ds' = random_symbolics ds 1 in
      try
        let sol = Srp.simulate_declarations ds' in
        if check_assertions sol then check_aux ds (iters - 1) num_rejected None
        else Some sol
      with Srp.Require_false ->
        incr num_rejected ;
        check_aux ds (iters - 1) num_rejected None

let check ds ~iterations : Solution.t option =
  let num_rejected = ref 0 in
  check_aux ds (iterations + 1) num_rejected None
