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

let smart_symbolic prog_constants map d =
  match d with
  | DSymbolic (x, te) ->
      let ty = match te with Exp e -> oget e.ety | Ty ty -> ty in
      let v =
        match StringMap.Exceptionless.find (Var.to_string x) map with
        | None -> random_value prog_constants default_max_map_size ty
        | Some v -> v
      in
      DSymbolic (x, Exp (e_val v))
  | _ -> d

let var_map ds =
  let map = ref StringMap.empty in
  List.iter
    (fun d ->
      match d with
      | DSymbolic (x, te) ->
          let ty =
            match te with Exp e -> oget e.ety | Ty ty -> ty
          in
          map := StringMap.add (Var.to_string x) (x, ty) !map
      | _ -> () )
    ds ;
  !map

let add_blocking_require info ds map var_map =
  let base = e_val (vbool true) in
  let e =
    StringMap.fold
      (fun x v acc ->
        let var, ty = StringMap.find x var_map in
        let var = evar var in
        let v = e_val v in
        let eq = eop UEq [var; v] in
        eop And [acc; eq] )
      map base
  in
  let neq = eop Not [e] in
  let d = DRequire neq in
  let ds = ds @ [d] in
  let ds = Typing.infer_declarations info ds in
  ds

(* let smart_symbolics info prog_constants var_map ds = *)
(*   (\* print_endline (Printing.declarations_to_string ds) ; *\) *)
(*   let map = Smt.symvar_assign ds in *)
(*   match map with *)
(*   | None -> (ds, None) *)
(*   | Some map -> *)
(*       let ds' = List.map (smart_symbolic prog_constants map) ds in *)
(*       (add_blocking_require info ds map var_map, Some ds') *)

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

(* let check_smart info ds ~iterations = *)
(*   let prog_constants = collect_all_values ds in *)
(*   let num_rejected = ref 0 in *)
(*   let generator ds = *)
(*     smart_symbolics info prog_constants (var_map ds) ds *)
(*   in *)
(*   let info = {decls= ds; iterations; num_rejected; generator} in *)
(*   check info iterations (ref 0) *)
