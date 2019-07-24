open Collections
open Syntax
open OCamlUtils

let default_value = BddMap.default_value

let rec default_value_exp ty =
  match ty with
  | TUnit -> exp_of_value (avalue (vunit (), Some ty, Span.default))
  | TBool -> exp_of_value (avalue (vbool false, Some ty, Span.default))
  | TNode -> exp_of_value (avalue (vnode 0, Some TNode, Span.default))
  | TEdge -> exp_of_value (avalue (vedge (0, 1), Some TEdge, Span.default))
  | TInt size ->
    exp_of_value (avalue (vint (Integer.create ~value:0 ~size:size), Some ty, Span.default))
  | TTuple ts ->
    aexp (etuple (BatList.map default_value_exp ts), Some ty, Span.default)
  | TRecord map -> aexp (etuple (BatList.map default_value_exp @@ RecordUtils.get_record_entries map),
                         Some ty, Span.default)
  | TOption _ ->
    exp_of_value (avalue (voption None, Some ty, Span.default))
  | TMap (ty1, ty2) ->
    aexp(eop MCreate [default_value_exp ty2], Some ty, Span.default)
  | TVar {contents= Link t} ->
    default_value_exp t
  | TVar _ | QVar _ | TArrow _ ->
    failwith "internal error (default_value)"

let rec random_value ~hints ~max_map_size ty =
  let i = Random.int 10 in
  match (TypeMap.find_opt ty hints, i < 9) with
  | Some vs, true ->
    let x = Random.int (ValueSet.cardinal vs) in
    List.nth (ValueSet.elements vs) x
  | _ ->
    match get_inner_type ty with
    | TUnit -> vunit ()
    | TBool -> vbool (Random.bool ())
    | TInt size ->
      let x = Integer.create_64 ~value:(Random.int64 Int64.max_int) ~size:size in
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
    | TRecord _ -> failwith "random_value: found record"
    | TArrow (ty1, ty2) -> failwith "unimplemented"
    | TNode | TEdge -> failwith "unimplemented (TODO)"

let random_symbolic hints max_map_size d =
  match d with
  | (x, te) ->
    let ty = match te with Ty ty -> ty | Exp e -> oget e.ety in
    let e = e_val (random_value hints max_map_size ty) in
    (* Printf.printf "Random for %s is now %s\n" (Var.to_string x)
       (Printing.exp_to_string e) ; *)
    (x, Exp e)

let random_symbolics ?hints ?max_map_size net =
  let hints =
    match hints with None -> TypeMap.empty | Some hs -> hs
  in
  let sz = match max_map_size with None -> 3 | Some x -> x in
  {net with symbolics=BatList.map (random_symbolic hints sz) net.symbolics}
