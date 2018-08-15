open Cudd
open Syntax
open Unsigned

(* TODO: 
    1. optimize variable ordering
    2. more efficient operations
    3. preprocessing of filter statements 
    4. map set and get operations *)

type t = Syntax.value Mtbdd.t

let mgr = Man.make_v ~numVars:32 ()

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
  match tb with Man.False | Man.Top -> false | Man.True -> true

let vars_to_value vars ty =
  let rec aux idx ty =
    match Typing.get_inner_type ty with
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

(* let res = User.map_op2
  ~commutative:true ~idempotent:true
  ~special:(fun bdd1 bdd2 ->
    if Vdd.is_cst bdd1 && Vdd.dval bdd1 = false then Some(bdd1)
    else if Vdd.is_cst bdd2 && Vdd.dval bdd2 = false then Some(bdd2)
    else None)
  (fun b1 b2 -> b1 && b2) *)

let map (f: value -> value) (vdd: t) : t =
  let g x = f (Mtbdd.get x) |> Mtbdd.unique tbl in
  Mapleaf.mapleaf1 g vdd

let map_when (pred: Bdd.vt -> bool) (f: value -> value) (vdd: t) : t =
  Mapleaf.combineleaf1
    ~default:(Vdd._background (Vdd.manager vdd))
    ~combine:Mapleaf.combineretractive
    (fun g leaf ->
      (g, if pred g then f (Mtbdd.get leaf) |> Mtbdd.unique tbl else leaf) )
    vdd

let map_when (pred: value -> bool) (f: value -> value) (vdd: t) (ty: ty) : t =
  let p bdd = pred (bdd_to_value bdd ty) in
  map_when p f vdd

let merge (f: value -> value -> value) (x: t) (y: t) : t =
  let g x y = f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique tbl in
  Mapleaf.mapleaf2 g x y

let find (map: t) (v: value) : value =
  let bdd = value_to_bdd v in
  let for_key = Mtbdd.constrain map bdd in
  Mtbdd.pick_leaf for_key

let update (map: t) (k: value) (v: value) : t =
  let leaf = Mtbdd.cst mgr tbl v in
  let key = value_to_bdd k in
  Mtbdd.ite key leaf map

let create (v: value) : t = Mtbdd.cst mgr tbl v

let bindings (map: t) (ty: ty) : (value * value) list =
  let bs = ref [] in
  Mtbdd.iter_cube
    (fun vars v ->
      (* Array.iteri (fun i x -> Printf.printf "vars %d is %b\n" i (tbool_to_bool x)) vars; *)
      let k = vars_to_value vars ty in
      bs := (k, v) :: !bs )
    map ;
  !bs

let from_bindings ((bs, default): (value * value) list * value) : t =
  failwith ""

let compare_maps bm1 bm2 = Mtbdd.topvar bm1 - Mtbdd.topvar bm2

let equal_maps bm1 bm2 = compare bm1 bm2 = 0

let hash_map bm = Mtbdd.topvar bm

let show_map bm ty =
  let bs = bindings bm ty in
  let str =
    List.fold_left
      (fun acc (k, v) ->
        let sep = if acc = "" then "" else ";" in
        Printf.sprintf "(%s,%s)%s%s"
          (Printing.value_to_string k)
          (Printing.value_to_string v)
          sep acc )
      "" bs
  in
  Printf.sprintf "[%s; ...]" str
