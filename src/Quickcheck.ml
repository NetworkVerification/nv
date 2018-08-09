open Collections
open Generators
open Syntax

let update_value map v =
  try
    let ty = Typing.strip_ty (oget v.vty) in
    let vs =
      match TypeMap.find_opt ty !map with
      | None -> ValueSet.empty
      | Some vs -> vs
    in
    map := TypeMap.add ty (ValueSet.add v vs) !map
  with _ -> ()

let collect_all_values ds : ValueSet.t TypeMap.t =
  let map = ref TypeMap.empty in
  Visitors.iter_exp_decls
    (fun _ e ->
      if Syntax.is_value e then
        let v = Syntax.to_value e in
        update_value map v
      else () )
    ds ;
  !map

let check_assertions (sol: Solution.t) =
  match sol.assertions with
  | None -> true
  | Some ass -> Graph.VertexMap.for_all (fun _ b -> b) ass

let rec check_aux ds prog_constants iters num_rejected acc =
  match (iters, acc) with
  | 0, _ | _, Some _ -> acc
  | _ ->
      let ds' = random_symbolics ~max_map_size:3 ~hints:prog_constants ds in
      try
        let sol = Srp.simulate_declarations ds' in
        if check_assertions sol then
          check_aux ds prog_constants (iters - 1) num_rejected None
        else Some sol
      with Srp.Require_false ->
        incr num_rejected ;
        check_aux ds prog_constants (iters - 1) num_rejected None

let check_random ds ~iterations : Solution.t option =
  let prog_constants = collect_all_values ds in
  let num_rejected = ref 0 in
  check_aux ds prog_constants (iterations + 1) num_rejected None
