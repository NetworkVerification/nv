open Cudd
open Syntax
open Unsigned

(* TODO: 
    1. optimize variable ordering
    2. more efficient operations
    3. preprocessing of filter statements *)

type t = Syntax.value Mtbdd.t * ty

let mgr = Man.make_v ()

let set_size sz =
  let num_vars = Man.get_bddvar_nb mgr in
  if num_vars < sz then
    for i = 1 to sz - num_vars do ignore (Bdd.newvar mgr) done

let ithvar i =
  set_size (i + 1) ;
  Bdd.ithvar mgr i

let rec ty_to_size ty =
  match Typing.get_inner_type ty with
  | TBool -> 1
  | TInt _ -> 32
  | TOption tyo -> 1 + ty_to_size tyo
  | TTuple ts -> List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
  | TArrow _ | TMap _ | TVar _ | QVar _ ->
      Console.error "internal error (ty_to_size)"

let tbl = Mtbdd.make_table ~hash:hash_value ~equal:equal_values

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

let map (f: value -> value) ((vdd, ty): t) : t =
  let g x = f (Mtbdd.get x) |> Mtbdd.unique tbl in
  (Mapleaf.mapleaf1 g vdd, ty)

let map_when (pred: Bdd.vt -> bool) (f: value -> value) ((vdd, ty): t) : t =
  ( Mapleaf.combineleaf1
      ~default:(Vdd._background (Vdd.manager vdd))
      ~combine:Mapleaf.combineretractive
      (fun g leaf ->
        (g, if pred g then f (Mtbdd.get leaf) |> Mtbdd.unique tbl else leaf) )
      vdd
  , ty )

let map_when (pred: value -> bool) (f: value -> value) ((vdd, ty): t) : t =
  let p bdd = pred (bdd_to_value bdd ty) in
  map_when p f (vdd, ty)

let merge (f: value -> value -> value) ((x, tyx): t) ((y, tyy): t) : t =
  let g x y = f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique tbl in
  (Mapleaf.mapleaf2 g x y, tyx)

let find ((map, _): t) (v: value) : value =
  let bdd = value_to_bdd v in
  let for_key = Mtbdd.constrain map bdd in
  Mtbdd.pick_leaf for_key

let update ((map, ty): t) (k: value) (v: value) : t =
  let leaf = Mtbdd.cst mgr tbl v in
  let key = value_to_bdd k in
  (Mtbdd.ite key leaf map, ty)

let create ~key_ty:ty (v: value) : t =
  set_size (ty_to_size ty) ;
  (Mtbdd.cst mgr tbl v, ty)

let count_tops arr =
  Array.fold_left
    (fun acc tb -> match tb with Man.Top -> acc + 1 | _ -> acc)
    0 arr

let pick_default_value map =
  let count = ref (-1) in
  let value = ref None in
  Mtbdd.iter_cube
    (fun vars v ->
      let c = count_tops vars in
      if c > !count then count := c ;
      value := Some v )
    map ;
  oget !value

let bindings ((map, ty): t) : (value * value) list * value =
  let bs = ref [] in
  let dv = pick_default_value map in
  Mtbdd.iter_cube
    (fun vars v ->
      (* Array.iteri (fun i x -> Printf.printf "vars %d is %b\n" i (tbool_to_bool x)) vars; *)
      if compare_values v dv <> 0 then
        let k = vars_to_value vars ty in
        bs := (k, v) :: !bs )
    map ;
  (!bs, dv)

let from_bindings ~key_ty:ty ((bs, default): (value * value) list * value) : t =
  let map = create ~key_ty:ty default in
  List.fold_left (fun acc (k, v) -> update acc k v) map bs

let compare_maps (bm1, _) (bm2, _) = Mtbdd.topvar bm1 - Mtbdd.topvar bm2

let equal_maps bm1 bm2 = compare bm1 bm2 = 0

let hash_map (bm, _) = Mtbdd.topvar bm

let show_map bm =
  let bs, dv = bindings bm in
  let str =
    List.fold_left
      (fun acc (k, v) ->
        let sep = if acc = "" then "" else ";" in
        Printf.sprintf "%s:=%s%s%s"
          (Printing.value_to_string k)
          (Printing.value_to_string v)
          sep acc )
      "" bs
  in
  let str = if str = "" then "" else str ^ ";...;" in
  Printf.sprintf "[%sdefault:=%s]" str (Printing.value_to_string dv)

module BddFunc = struct
  type bdd_index = Bdd.vt

  type bdd_value =
    | BBool of bdd_index
    | BInt of bdd_index array
    | BTuple of bdd_value list
    | BOption of bdd_index * bdd_value

  let bdd_of_bool b = if b then Bdd.dtrue mgr else Bdd.dfalse mgr

  let create_value (ty: ty) : bdd_value =
    let rec aux i ty =
      match Typing.get_inner_type ty with
      | TBool -> (BBool (ithvar i), i + 1)
      | TInt _ -> (BInt (Array.init 32 (fun j -> ithvar (i + j))), i + 32)
      | TTuple ts ->
          let bs, idx =
            List.fold_left
              (fun (ls, idx) t ->
                let v, i = aux idx t in
                (v :: ls, i) )
              ([], i) ts
          in
          (BTuple (List.rev bs), idx)
      | TOption ty ->
          let v, idx = aux (i + 1) ty in
          (BOption (ithvar i, v), idx)
      | TArrow _ | QVar _ | TVar _ | TMap _ ->
          Console.error "internal error (create_value)"
    in
    let ret, _ = aux 0 ty in
    ret

  let rec ite (b: Bdd.vt) (x: bdd_value) (y: bdd_value) : bdd_value =
    match (x, y) with
    | BBool m, BBool n -> BBool (Bdd.ite b m n)
    | BInt ms, BInt ns ->
        let both = List.combine (Array.to_list ms) (Array.to_list ns) in
        let ite = List.map (fun (m, n) -> Bdd.ite b m n) both in
        BInt (Array.of_list ite)
    | BOption (tag1, m), BOption (tag2, n) ->
        let tag = Bdd.ite b tag1 tag2 in
        BOption (tag, ite b m n)
    | BTuple ms, BTuple ns ->
        let both = List.combine ms ns in
        let ite = List.map (fun (m, n) -> ite b m n) both in
        BTuple ite
    | _ -> Console.error "internal error (ite)"

  let rec eq (x: bdd_value) (y: bdd_value) : bdd_value =
    let rec aux x y : Bdd.vt =
      match (x, y) with
      | BBool b1, BBool b2 -> Bdd.eq b1 b2
      | BInt bs1, BInt bs2 ->
          let both = List.combine (Array.to_list bs1) (Array.to_list bs2) in
          List.fold_left
            (fun acc (b1, b2) -> Bdd.dand acc (Bdd.eq b1 b2))
            (Bdd.dtrue mgr) both
      | BOption (tag1, b1), BOption (tag2, b2) ->
          let tags = Bdd.eq tag1 tag2 in
          let values = aux b1 b2 in
          Bdd.dand tags values
      | BTuple bs1, BTuple bs2 ->
          let both = List.combine bs1 bs2 in
          List.fold_left
            (fun acc (b1, b2) -> Bdd.dand acc (aux b1 b2))
            (Bdd.dtrue mgr) both
      | _ -> Console.error "internal error (eq)"
    in
    BBool (aux x y)

  let add (x: bdd_value) (y: bdd_value) : bdd_value =
    let aux xs ys =
      let var3 = ref (Bdd.dfalse mgr) in
      let var4 = Array.make 32 (Bdd.dfalse mgr) in
      for var5 = Array.length xs - 1 downto 0 do
        var4.(var5) <- Bdd.xor xs.(var5) ys.(var5) ;
        var4.(var5) <- Bdd.xor var4.(var5) !var3 ;
        let var6 = Bdd.dor xs.(var5) ys.(var5) in
        let var6 = Bdd.dand var6 !var3 in
        let var7 = Bdd.dand xs.(var5) ys.(var5) in
        let var7 = Bdd.dor var7 var6 in
        var3 := var7
      done ;
      var4
    in
    match (x, y) with
    | BInt xs, BInt ys -> BInt (aux xs ys)
    | _ -> Console.error "internal error (add)"

  let cmp (eq: bool) (x: bdd_value) (y: bdd_value) : bdd_value =
    let less x y = Bdd.dand (Bdd.dnot x) y in
    let aux (xs: bdd_index array) ys =
      let acc = ref (Bdd.dfalse mgr) in
      for i = Array.length xs - 1 downto 0 do
        let x, y = (xs.(i), ys.(i)) in
        let z = if eq then Bdd.dand !acc (Bdd.eq x y) else !acc in
        acc := Bdd.dor (less x y) z
      done ;
      !acc
    in
    match (x, y) with
    | BInt xs, BInt ys -> BBool (aux xs ys)
    | _ -> Console.error "internal error (leq)"

  let rec eval (env: bdd_value Env.t) (e: exp) : bdd_value =
    match e.e with
    | ETy (e1, _) -> eval env e1
    | EVar x -> (
      match Env.lookup_opt env x with
      | None -> Console.error "internal error (eval)"
      | Some v -> v )
    | EVal v -> eval_value env v
    | EOp (op, es) -> (
      match (op, es) with
      | And, [e1; e2] -> eval_bool_op2 env Bdd.dand e1 e2
      | Or, [e1; e2] -> eval_bool_op2 env Bdd.dor e1 e2
      | Not, [e1] -> eval_bool_op1 env Bdd.dnot e1
      | UEq, [e1; e2] -> eq (eval env e1) (eval env e2)
      | UAdd, [e1; e2] -> add (eval env e1) (eval env e2)
      | USub, [e1; e2] -> Console.error "subtraction not implemented"
      | ULess, [e1; e2] -> cmp false (eval env e1) (eval env e2)
      | ULeq, [e1; e2] -> cmp true (eval env e1) (eval env e2)
      | _ -> Console.error "internal error (eval)" )
    | EIf (e1, e2, e3) -> (
        let v1 = eval env e1 in
        let v2 = eval env e2 in
        let v3 = eval env e3 in
        match v1 with
        | BBool b -> ite b v2 v3
        | _ -> Console.error "internal error (eval)" )
    | ELet (x, e1, e2) ->
        let v1 = eval env e1 in
        eval (Env.update env x v1) e2
    | ETuple es ->
        let vs = List.map (eval env) es in
        BTuple vs
    | ESome e -> BOption (Bdd.dtrue mgr, eval env e)
    | EMatch (e1, brances) -> failwith ""
    | EFun _ | EApp _ -> failwith ""

  and eval_bool_op1 env f e1 =
    let v1 = eval env e1 in
    match v1 with
    | BBool b1 -> BBool (f b1)
    | _ -> Console.error "internal error (eval)"

  and eval_bool_op2 env f e1 e2 =
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    match (v1, v2) with
    | BBool b1, BBool b2 -> BBool (f b1 b2)
    | _ -> Console.error "internal error (eval)"

  and eval_value env (v: value) =
    match v.v with
    | VBool b -> BBool (bdd_of_bool b)
    | VUInt32 i ->
        let bs =
          Array.init 32 (fun j ->
              let bit = get_bit i j in
              bdd_of_bool bit )
        in
        BInt bs
    | VOption None ->
        let ty =
          match Typing.get_inner_type (oget v.vty) with
          | TOption ty -> ty
          | _ -> Console.error "internal error (eval_value)"
        in
        let dv = Generators.default_value ty in
        BOption (Bdd.dfalse mgr, eval_value env dv)
    | VOption (Some v) -> BOption (Bdd.dtrue mgr, eval_value env v)
    | VTuple vs -> BTuple (List.map (eval_value env) vs)
    | VMap _ | VClosure _ -> Console.error "internal error (eval_value)"
end
