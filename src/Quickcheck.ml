open Generators

let check_assertions (sol: Solution.t) =
  match sol.assertions with
  | None -> true
  | Some ass -> Graph.VertexMap.for_all (fun _ b -> b) ass

let rec check_aux ds iters num_rejected acc =
  match (iters, acc) with
  | 0, _ | _, Some _ -> acc
  | _ ->
      let ds' = random_symbolics ~max_map_size:1 ds in
      try
        let sol = Srp.simulate_declarations ds' in
        if check_assertions sol then check_aux ds (iters - 1) num_rejected None
        else Some sol
      with Srp.Require_false ->
        incr num_rejected ;
        check_aux ds (iters - 1) num_rejected None

let check_random ds ~iterations : Solution.t option =
  let num_rejected = ref 0 in
  check_aux ds (iterations + 1) num_rejected None
