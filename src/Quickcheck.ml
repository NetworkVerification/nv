open Collections
open Generators
open Syntax
open Slicing

let default_max_map_size = 4

type check_info =
  { net: network
  ; iterations: int
  ; num_rejected: int ref
  ; generator: network -> network * network option }

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

let collect_all_values net : ValueSet.t TypeMap.t =
  let map = ref TypeMap.empty in
  Visitors.iter_exp_net
    (fun e ->
      if Syntax.is_value e then
        let v = Syntax.to_value e in
        update_value map v
      else () )
    net ;
  !map

let check_assertions (sol: Solution.t) =
  match sol.assertions with
  | None -> true
  | Some ass -> AdjGraph.VertexMap.for_all (fun _ b -> b) ass

let rec check_aux info iters acc =
  match (info.iterations, acc) with
  | 0, _ | _, Some _ -> acc
  | _ ->
      let net, net' = info.generator info.net in
      let info = {info with net= net} in
      match net' with
      | None -> None
      | Some net' ->
        try
          let sol = Srp.simulate_net net' in
          if check_assertions sol then
            check_aux
              {info with iterations= info.iterations - 1}
              iters None
          else Some (sol, iters - info.iterations + 1)
        with Srp.Require_false ->
          incr info.num_rejected ;
          check_aux
            {info with iterations= info.iterations - 1}
            iters None

let smart_symbolic prog_constants map symb =
  let (x, te) = symb in
  let ty = match te with Exp e -> oget e.ety | Ty ty -> ty in
  let v =
    match VarMap.Exceptionless.find x map with
    | None -> random_value prog_constants default_max_map_size ty
    | Some v -> v
  in
  (x, Exp (aexp(e_val v, Some ty, Span.default)))

(* Given a network return a map from its symbolic values to their types *)
let var_map net =
  let map = ref VarMap.empty in
  BatList.iter
    (fun (x,te) ->
      let ty =
        match te with Exp e -> oget e.ety | Ty ty -> ty
      in
      map := VarMap.add x (x, ty) !map) net.symbolics ;
  !map

let add_blocking_require info net map var_map =
  let base = aexp(e_val (avalue (vbool true, Some TBool, Span.default)), Some TBool, Span.default) in
  let e =
    VarMap.fold
      (fun x v acc ->
        let var, ty = VarMap.find x var_map in
        let var = aexp(evar var, Some ty, Span.default) in
        let v = aexp(e_val (avalue (v, Some ty, Span.default)), Some ty, Span.default) in
        let eq = aexp(eop UEq [var; v], Some TBool, Span.default) in
        aexp(eop And [acc; eq], Some TBool, Span.default))
          map base
  in
  let neq = aexp(eop Not [e], Some TBool, Span.default) in
  {net with requires = neq :: net.requires}

let smart_symbolics info prog_constants var_map net =
  (* print_endline (Printing.declarations_to_string ds) ; *)
  let map = Smt.symvar_assign info net in
  match map with
  | None -> (net, None)
  | Some map ->
     (add_blocking_require info net map var_map,
      Some {net with symbolics = BatList.map (smart_symbolic prog_constants map) net.symbolics})

type check_stats = {iterations: int; num_rejected: int}

let check info iterations num_rejected =
  let result = check_aux info iterations None in
  let info = {iterations; num_rejected= !num_rejected} in
  match result with
  | None -> (None, info)
  | Some (sol, iters) -> (Some sol, {info with iterations= iters})

let check_random net ~iterations =
  let prog_constants = collect_all_values net in
  let num_rejected = ref 0 in
  let generator net =
    let net' =
      random_symbolics ~max_map_size:default_max_map_size
        ~hints:prog_constants net
    in
    (net, Some net')
  in
  let info = {net= net; iterations; num_rejected; generator} in
  check info iterations num_rejected

let check_smart info net ~iterations =
  let prog_constants = collect_all_values net in
  let num_rejected = ref 0 in
  let generator net =
    smart_symbolics info prog_constants (var_map net) net
  in
  let info = {net; iterations; num_rejected; generator} in
  check info iterations (ref 0)
