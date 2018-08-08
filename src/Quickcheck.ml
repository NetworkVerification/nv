open Random
open Syntax
open Unsigned

(* TODO: add a hints option to bias for constants that appear in the program *)

let rec random_value ty (depth: int) =
  match Typing.get_inner_type ty with
  | TBool -> VBool (Random.bool ()) |> value
  | TInt _ ->
      let x = UInt32.of_int64 (Random.int64 Int64.max_int) in
      VUInt32 x |> value
  | TTuple ts ->
      VTuple (List.map (fun ty -> random_value ty (depth + 1)) ts) |> value
  | TOption ty ->
      let b = Random.bool () in
      if b then VOption None |> value
      else VOption (Some (random_value ty (depth + 1))) |> value
  | TMap (ty1, ty2) ->
      let default = random_value ty2 (depth + 1) in
      let map = IMap.create compare_values default in
      VMap map |> value
  | QVar _ | TVar _ -> failwith ""
  | TArrow (ty1, ty2) -> failwith ""

let random_symbolic d =
  match d with
  | DSymbolic (x, te) ->
      let ty = match te with Ty ty -> ty | Exp e -> oget e.ety in
      let e = EVal (random_value ty 10) |> exp in
      DSymbolic (x, Exp e)
  | _ -> d

let random_symbolics ds = List.map random_symbolic ds

let check_assertions (sol: Solution.t) =
  match sol.assertions with
  | None -> true
  | Some ass -> Graph.VertexMap.for_all (fun _ b -> b) ass

let rec check_aux ds iters acc =
  match (iters, acc) with
  | 0, _ | _, Some _ -> acc
  | _ ->
      let ds = random_symbolics ds in
      let sol = Srp.simulate_declarations ds in
      if check_assertions sol then None else Some sol

let check ds ~iterations : Solution.t option =
  check_aux ds (iterations + 1) None
