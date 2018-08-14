open Cudd
open Syntax
open Unsigned

(* TODO: 
    1. optimize variable ordering
    2. more efficient operations
    3. preprocessing of filter statements 
    4. map set and get operations *)

type bdd_map = {map: Syntax.value Mtbdd.t; ty: ty}

let mgr = Man.make_v ()

(* Mtbdd.cst manager tbl 3 *)

let tbl = Mtbdd.make_table ~hash:hash_value ~equal:equal_values

let nth_bit x i = x land (1 lsl i) <> 0

let get_bit (x: UInt32.t) (i: int) : bool =
  let x = UInt32.to_int x in
  nth_bit x i

let mk_int i idx =
  let acc = ref (Bdd.dtrue mgr) in
  for j = 0 to 31 do
    let var = Bdd.ithvar mgr (idx + j) in
    let bit = get_bit i j in
    let bdd = if bit then Bdd.dtrue mgr else Bdd.dfalse mgr in
    acc := Bdd.dand !acc (Bdd.eq var bdd)
  done ;
  !acc

let value_to_bdd (v: value) : Bdd.vt =
  let rec aux v idx =
    match v.v with
    | VBool b ->
        let var = Bdd.ithvar mgr idx in
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
        let var = Bdd.ithvar mgr idx in
        let tag = Bdd.eq var (Bdd.dfalse mgr) in
        let dv = Generators.default_value (oget v.vty) in
        let value, idx = aux dv (idx + 1) in
        (Bdd.dand tag value, idx)
    | VOption (Some dv) ->
        let var = Bdd.ithvar mgr idx in
        let tag = Bdd.eq var (Bdd.dfalse mgr) in
        let value, idx = aux dv (idx + 1) in
        (Bdd.dand tag value, idx)
    | VMap _ | VClosure _ -> Console.error "internal error (value_to_bdd)"
  in
  let bdd, _ = aux v 0 in
  bdd

let tbool_to_bool tb =
  match tb with Man.False -> false | Man.True | Man.Top -> true

let bdd_to_value (guard: Bdd.vt) (ty: ty) : value =
  let vars = Bdd.pick_minterm guard in
  let rec aux idx ty =
    match Typing.get_inner_type ty with
    | TBool -> (VBool (tbool_to_bool vars.(idx)) |> value, idx + 1)
    | TInt _ -> failwith ""
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

(* let res = User.map_op2
  ~commutative:true ~idempotent:true
  ~special:(fun bdd1 bdd2 ->
    if Vdd.is_cst bdd1 && Vdd.dval bdd1 = false then Some(bdd1)
    else if Vdd.is_cst bdd2 && Vdd.dval bdd2 = false then Some(bdd2)
    else None)
  (fun b1 b2 -> b1 && b2) *)

let map (f: value -> value) ({map= vdd; ty}: bdd_map) : bdd_map =
  let g x = f (Mtbdd.get x) |> Mtbdd.unique tbl in
  let map = Mapleaf.mapleaf1 g vdd in
  {map; ty}

let mapWhen (pred: Bdd.vt -> bool) (f: value -> value)
    ({map= vdd; ty}: bdd_map) : bdd_map =
  let map =
    Mapleaf.combineleaf1
      ~default:(Vdd._background (Vdd.manager vdd))
      ~combine:Mapleaf.combineretractive
      (fun g leaf ->
        (g, if pred g then f (Mtbdd.get leaf) |> Mtbdd.unique tbl else leaf) )
      vdd
  in
  {map; ty}

let merge (f: value -> value -> value) ({map= x; ty= ty1}: bdd_map)
    ({map= y; ty= ty2}: bdd_map) : bdd_map =
  let g x y = f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique tbl in
  let map = Mapleaf.mapleaf2 g x y in
  {map; ty= ty1}
