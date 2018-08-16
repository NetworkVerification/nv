open Cudd
open Syntax
open Unsigned

let mgr = Man.make_v ()

let set_size sz =
  let num_vars = Man.get_bddvar_nb mgr in
  if num_vars < sz then
    for i = 1 to sz - num_vars do ignore (Bdd.newvar mgr) done

let ithvar i =
  set_size (i + 1) ;
  Bdd.ithvar mgr i

let rec ty_to_size ty =
  match get_inner_type ty with
  | TBool -> 1
  | TInt _ -> 32
  | TOption tyo -> 1 + ty_to_size tyo
  | TTuple ts -> List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
  | TArrow _ | TMap _ | TVar _ | QVar _ ->
      Console.error "internal error (ty_to_size)"

let tbl = Mtbdd.make_table ~hash:hash_value ~equal:equal_values

let tbl_bool =
  Mtbdd.make_table ~hash:(fun b -> if b then 1 else 0) ~equal:( = )

let nth_bit x i = x land (1 lsl i) <> 0

let get_bit (x: UInt32.t) (i: int) : bool =
  let x = UInt32.to_int x in
  nth_bit x i

let mk_int i idx =
  let acc = ref (Bdd.dtrue mgr) in
  for j = 0 to 31 do
    let var = ithvar (idx + j) in
    let bit = get_bit i j in
    let bdd = if bit then Bdd.dtrue mgr else Bdd.dfalse mgr in
    acc := Bdd.dand !acc (Bdd.eq var bdd)
  done ;
  !acc

let value_to_bdd (v: value) : Bdd.vt =
  let rec aux v idx =
    match v.v with
    | VBool b ->
        let var = ithvar idx in
        ((if b then var else Bdd.dnot var), idx + 1)
    | VUInt32 i -> (mk_int i idx, idx + 32)
    | VTuple vs ->
        let base = Bdd.dtrue mgr in
        List.fold_left
          (fun (bdd_acc, idx) v ->
            let bdd, i = aux v idx in
            (Bdd.dand bdd_acc bdd, i) )
          (base, idx) vs
    | VOption None ->
        let var = ithvar idx in
        let tag = Bdd.eq var (Bdd.dfalse mgr) in
        let dv = Generators.default_value (oget v.vty) in
        let value, idx = aux dv (idx + 1) in
        (Bdd.dand tag value, idx)
    | VOption (Some dv) ->
        let var = ithvar idx in
        let tag = Bdd.eq var (Bdd.dtrue mgr) in
        let value, idx = aux dv (idx + 1) in
        (Bdd.dand tag value, idx)
    | VMap _ | VClosure _ -> Console.error "internal error (value_to_bdd)"
  in
  let bdd, _ = aux v 0 in
  bdd

let tbool_to_bool tb =
  match tb with Man.False | Man.Top -> false | Man.True -> true

let vars_to_value vars ty =
  let rec aux idx ty =
    match get_inner_type ty with
    | TBool -> (VBool (tbool_to_bool vars.(idx)) |> value, idx + 1)
    | TInt _ ->
        let acc = ref UInt32.zero in
        for i = 0 to 31 do
          let bit = tbool_to_bool vars.(idx + i) in
          if bit then
            let add = UInt32.shift_left UInt32.one i in
            acc := UInt32.add !acc add
        done ;
        (value (VUInt32 !acc), idx + 32)
    | TTuple ts ->
        let vs, i =
          List.fold_left
            (fun (vs, idx) ty ->
              let v, i = aux idx ty in
              (v :: vs, i) )
            ([], idx) ts
        in
        (value (VTuple (List.rev vs)), i)
    | TOption tyo ->
        let tag = tbool_to_bool vars.(idx) in
        let v, i = aux (idx + 1) tyo in
        let v =
          if tag then VOption (Some v) |> value else value (VOption None)
        in
        (v, i)
    | TArrow _ | TMap _ | TVar _ | QVar _ ->
        Console.error "internal error (bdd_to_value)"
  in
  fst (aux 0 ty)

let bdd_to_value (guard: Bdd.vt) (ty: ty) : value =
  let vars = Bdd.pick_minterm guard in
  vars_to_value vars ty
