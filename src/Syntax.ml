(* Abstract syntax of SRP attribute processing expressions *)
open BatMap
open Cudd
open Unsigned

let optimize_bdd_ops = true

(* indices into maps or map sizes must be static constants *)
type index = UInt32.t

(* see:  http://okmij.org/ftp/ML/generalization.html *)
type level = int

type tyname = Var.t

type ty =
  | TVar of tyvar ref
  | QVar of tyname
  | TBool
  | TInt of index
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty

and tyvar = Unbound of tyname * level | Link of ty

type var = Var.t

type op =
  | And
  | Or
  | Not
  | UAdd
  | USub
  | UEq
  | ULess
  | ULeq
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMerge
  | MFilter

type pattern =
  | PWild
  | PVar of var
  | PBool of bool
  | PUInt32 of UInt32.t
  | PTuple of pattern list
  | POption of pattern option

type v =
  | VBool of bool
  | VUInt32 of UInt32.t
  | VMap of mtbdd
  | VTuple of value list
  | VOption of value option
  | VClosure of closure

and mtbdd = (value Mtbdd.t * ty)

and value = {v: v; vty: ty option; vspan: Span.t}

and e =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | ESome of exp
  | EMatch of exp * branches
  | ETy of exp * ty

and exp = {e: e; ety: ty option; espan: Span.t}

and branches = (pattern * exp) list

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and closure = (env * func)

and env = {ty: ty Env.t; value: value Env.t}

and ty_or_exp = Ty of ty | Exp of exp

type declaration =
  | DLet of var * ty option * exp
  | DSymbolic of var * ty_or_exp
  | DATy of ty
  | DMerge of exp
  | DTrans of exp
  | DInit of exp
  | DAssert of exp
  | DRequire of exp
  | DNodes of UInt32.t
  | DEdges of (UInt32.t * UInt32.t) list

type declarations = declaration list

(* Utilities *)

let arity op =
  match op with
  | And -> 2
  | Or -> 2
  | Not -> 1
  | UAdd -> 2
  | USub -> 2
  | UEq -> 2
  | ULess -> 2
  | ULeq -> 2
  | MCreate -> 1
  | MGet -> 2
  | MSet -> 3
  | MMap -> 2
  | MMerge -> 3
  | MFilter -> 2

(* Useful constructors *)

let tint = TInt (UInt32.of_int 32)

let exp (e: e) : exp = {e; ety= None; espan= Span.default}

let wrap exp e = {e; ety= exp.ety; espan= exp.espan}

let value (v: v) : value = {v; vty= None; vspan= Span.default}

let e_val (x: v) : exp = exp (EVal (value x))

let func x body = {arg= x; argty= None; resty= None; body}

let lam x body = exp (EFun (func x body))

let annot ty e = {e= e.e; ety= Some ty; espan= e.espan}

let annotv ty v = {v= v.v; vty= Some ty; vspan= v.vspan}

let rec is_value e =
  match e.e with
  | EVal _ -> true
  | ETuple es -> List.for_all is_value es
  | ESome e -> is_value e
  | _ -> false

let rec to_value e =
  match e.e with
  | EVal v -> v
  | ETuple es ->
      {v= VTuple (List.map to_value es); vspan= e.espan; vty= e.ety}
  | ESome e1 ->
      {v= VOption (Some (to_value e1)); vspan= e.espan; vty= e.ety}
  | _ -> failwith "internal error (to_value)"

let oget (x: 'a option) : 'a =
  match x with
  | None -> failwith "internal error (oget)"
  | Some y -> y

let rec lams params body =
  match params with
  | [] -> failwith "lams: no parameters"
  | [p] -> lam p body
  | p :: params -> lam p (lams params body)

let rec apps f args : exp =
  match args with
  | [] -> failwith "apps: no arguments"
  | [a] -> exp (EApp (f, a))
  | a :: args -> apps (exp (EApp (f, a))) args

let apply_closure cl (args: value list) =
  apps (e_val (VClosure cl)) (List.map (fun a -> exp (EVal a)) args)

let get_decl ds f =
  try
    let daty : declaration =
      List.find
        (fun d -> match f d with None -> false | Some _ -> true)
        ds
    in
    f daty
  with _ -> None

let get_attr_type ds =
  get_decl ds (fun d -> match d with DATy ty -> Some ty | _ -> None)

let get_merge ds =
  get_decl ds (fun d -> match d with DMerge e -> Some e | _ -> None)

let get_trans ds =
  get_decl ds (fun d -> match d with DTrans e -> Some e | _ -> None)

let get_init ds =
  get_decl ds (fun d -> match d with DInit e -> Some e | _ -> None)

let get_assert ds =
  get_decl ds (fun d ->
      match d with DAssert e -> Some e | _ -> None )

let get_edges ds =
  get_decl ds (fun d ->
      match d with DEdges es -> Some es | _ -> None )

let get_nodes ds =
  get_decl ds (fun d -> match d with DNodes i -> Some i | _ -> None)

let get_symbolics ds =
  List.fold_left
    (fun acc d ->
      match d with DSymbolic (x, e) -> (x, e) :: acc | _ -> acc )
    [] ds
  |> List.rev

let get_requires ds =
  List.fold_left
    (fun acc d -> match d with DRequire e -> e :: acc | _ -> acc)
    [] ds
  |> List.rev

let rec equal_values (v1: value) (v2: value) = equal_vs v1.v v2.v

and equal_vs v1 v2 =
  match (v1, v2) with
  | VBool b1, VBool b2 -> b1 = b2
  | VUInt32 i1, VUInt32 i2 -> UInt32.compare i1 i2 = 0
  | VMap (m1, _), VMap (m2, _) -> Mtbdd.is_equal m1 m2
  | VTuple vs1, VTuple vs2 -> equal_lists vs1 vs2
  | VOption vo1, VOption vo2 -> (
    match (vo1, vo2) with
    | None, None -> true
    | None, Some _ -> false
    | Some _, None -> false
    | Some x, Some y -> equal_values x y )
  | VClosure (e1, f1), VClosure (e2, f2) ->
      let {ty= ty1; value= value1} = e1 in
      let {ty= ty2; value= value2} = e2 in
      let cmp = Env.compare Pervasives.compare ty1 ty1 in
      if cmp <> 0 then false
      else
        let cmp = Env.equal equal_values value1 value2 in
        cmp && equal_funcs f1 f2
  | _, _ -> false

(* TODO: check equal expressions *)
and equal_funcs f1 f2 =
  let {arg= x; argty= tyx; resty= resx; body= e1} = f1 in
  let {arg= y; argty= tyy; resty= resy; body= e2} = f2 in
  Var.equals x y

and equal_lists vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> true
  | [], _ | _, [] -> false
  | v1 :: vs1, v2 :: vs2 -> equal_values v1 v2 && equal_lists vs1 vs2

let rec hash_value v =
  match v.v with
  | VBool b -> if b then 1 else 0
  | VUInt32 i -> UInt32.to_int i
  | VMap m -> failwith "unimplemented map hashl"
  | VTuple vs ->
      List.fold_left (fun acc v -> (31 * acc) + hash_value v) 0 vs
  | VOption vo -> (
    match vo with None -> 5 | Some x -> 7 + (31 * hash_value x) )
  | VClosure (e1, f1) ->
      let {ty= ty1; value= v} = e1 in
      let vs = Env.to_list v in
      List.fold_left
        (fun acc (x, v) ->
          let x = Hashtbl.hash (Var.to_string x) in
          (31 * acc) + (5 * x) + hash_value v )
        0 vs

let rec get_inner_type t : ty =
  match t with TVar {contents= Link t} -> get_inner_type t | _ -> t

(* Include the map type here to avoid circular dependency *)

module BddUtils = struct
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
    | TTuple ts ->
        List.fold_left (fun acc t -> acc + ty_to_size t) 0 ts
    | TArrow _ | TMap _ | TVar _ | QVar _ ->
        failwith "internal error (ty_to_size)"

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

  let tbool_to_bool tb =
    match tb with Man.False | Man.Top -> false | Man.True -> true
end

module BddMap = struct
  module B = BddUtils

  (* TODO: 
      1. optimize variable ordering
      2. more efficient operations
      3. preprocessing of filter statements *)

  type t = mtbdd

  (* let res = User.map_op2
    ~commutative:true ~idempotent:true
    ~special:(fun bdd1 bdd2 ->
      if Vdd.is_cst bdd1 && Vdd.dval bdd1 = false then Some(bdd1)
      else if Vdd.is_cst bdd2 && Vdd.dval bdd2 = false then Some(bdd2)
      else None)
    (fun b1 b2 -> b1 && b2) *)

  let create ~key_ty:ty (v: value) : t =
    B.set_size (B.ty_to_size ty) ;
    (Mtbdd.cst B.mgr B.tbl v, ty)

  let rec default_value ty =
    let v =
      match ty with
      | TBool -> VBool false
      | TInt _ -> VUInt32 (UInt32.of_int 0)
      | TTuple ts -> VTuple (List.map default_value ts)
      | TOption ty -> VOption None
      | TMap (ty1, ty2) ->
          VMap (create ~key_ty:ty1 (default_value ty2))
      | TVar _ | QVar _ | TArrow _ ->
          failwith "internal error (default_value)"
    in
    value v

  let value_to_bdd (v: value) : Bdd.vt =
    let rec aux v idx =
      match v.v with
      | VBool b ->
          let var = B.ithvar idx in
          ((if b then var else Bdd.dnot var), idx + 1)
      | VUInt32 i -> (B.mk_int i idx, idx + 32)
      | VTuple vs ->
          let base = Bdd.dtrue B.mgr in
          List.fold_left
            (fun (bdd_acc, idx) v ->
              let bdd, i = aux v idx in
              (Bdd.dand bdd_acc bdd, i) )
            (base, idx) vs
      | VOption None ->
          let var = B.ithvar idx in
          let tag = Bdd.eq var (Bdd.dfalse B.mgr) in
          let dv = default_value (oget v.vty) in
          let value, idx = aux dv (idx + 1) in
          (Bdd.dand tag value, idx)
      | VOption (Some dv) ->
          let var = B.ithvar idx in
          let tag = Bdd.eq var (Bdd.dtrue B.mgr) in
          let value, idx = aux dv (idx + 1) in
          (Bdd.dand tag value, idx)
      | VMap _ | VClosure _ ->
          failwith "internal error (value_to_bdd)"
    in
    let bdd, _ = aux v 0 in
    bdd

  let vars_to_value vars ty =
    let rec aux idx ty =
      let v, i =
        match get_inner_type ty with
        | TBool ->
            (VBool (B.tbool_to_bool vars.(idx)) |> value, idx + 1)
        | TInt _ ->
            let acc = ref UInt32.zero in
            for i = 0 to 31 do
              let bit = B.tbool_to_bool vars.(idx + i) in
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
            let tag = B.tbool_to_bool vars.(idx) in
            let v, i = aux (idx + 1) tyo in
            let v =
              if tag then VOption (Some v) |> value
              else value (VOption None)
            in
            (v, i)
        | TArrow _ | TMap _ | TVar _ | QVar _ ->
            failwith "internal error (bdd_to_value)"
      in
      (annotv ty v, i)
    in
    fst (aux 0 ty)

  let bdd_to_value (guard: Bdd.vt) (ty: ty) : value =
    let vars = Bdd.pick_minterm guard in
    vars_to_value vars ty

  let map_cache = Memo.Cache (Cache.create1 ())

  let map (f: value -> value) ((vdd, ty): t) : t =
    let g x = f (Mtbdd.get x) |> Mtbdd.unique B.tbl in
    if optimize_bdd_ops then
      let res = User.map_op1 ~memo:map_cache g in
      (res vdd, ty)
    else (Mapleaf.mapleaf1 g vdd, ty)

  let map_when_cache = Memo.Cache (Cache.create2 ())

  let map_when (pred: Bdd.vt) (f: value -> value) ((vdd, ty): t) : t =
    let g b v =
      if Mtbdd.get b then f (Mtbdd.get v) |> Mtbdd.unique B.tbl
      else v
    in
    let tru = Mtbdd.cst B.mgr B.tbl_bool true in
    let fal = Mtbdd.cst B.mgr B.tbl_bool false in
    let pred = Mtbdd.ite pred tru fal in
    if optimize_bdd_ops then
      let res =
        User.map_op2 ~memo:map_when_cache ~commutative:false
          ~idempotent:false g
      in
      (res pred vdd, ty)
    else (Mapleaf.mapleaf2 g pred vdd, ty)

  let merge_cache = Memo.Cache (Cache.create2 ())

  let merge (f: value -> value -> value) ((x, tyx): t) ((y, tyy): t)
      : t =
    let g x y =
      f (Mtbdd.get x) (Mtbdd.get y) |> Mtbdd.unique B.tbl
    in
    if optimize_bdd_ops then
      let res =
        User.map_op2 ~memo:merge_cache ~commutative:false
          ~idempotent:false g
      in
      (res x y, tyx)
    else (Mapleaf.mapleaf2 g x y, tyx)

  let find ((map, _): t) (v: value) : value =
    let bdd = value_to_bdd v in
    let for_key = Mtbdd.constrain map bdd in
    Mtbdd.pick_leaf for_key

  let update ((map, ty): t) (k: value) (v: value) : t =
    let leaf = Mtbdd.cst B.mgr B.tbl v in
    let key = value_to_bdd k in
    (Mtbdd.ite key leaf map, ty)

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
        if not (equal_values v dv) then
          let k = vars_to_value vars ty in
          bs := (k, v) :: !bs )
      map ;
    (!bs, dv)

  let from_bindings ~key_ty:ty
      ((bs, default): (value * value) list * value) : t =
    let map = create ~key_ty:ty default in
    List.fold_left (fun acc (k, v) -> update acc k v) map bs

  let equal (bm1, _) (bm2, _) = Mtbdd.is_equal bm1 bm2
end

module BddFunc = struct
  module B = BddUtils

  type t =
    | BBool of Bdd.vt
    | BInt of Bdd.vt array
    | BTuple of t list
    | BOption of Bdd.vt * t

  let bdd_of_bool b = if b then Bdd.dtrue B.mgr else Bdd.dfalse B.mgr

  let create_value (ty: ty) : t =
    let rec aux i ty =
      match get_inner_type ty with
      | TBool -> (BBool (B.ithvar i), i + 1)
      | TInt _ ->
          (BInt (Array.init 32 (fun j -> B.ithvar (i + j))), i + 32)
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
          (BOption (B.ithvar i, v), idx)
      | TArrow _ | QVar _ | TVar _ | TMap _ ->
          failwith "internal error (create_value)"
    in
    let ret, _ = aux 0 ty in
    ret

  let rec ite (b: Bdd.vt) (x: t) (y: t) : t =
    match (x, y) with
    | BBool m, BBool n -> BBool (Bdd.ite b m n)
    | BInt ms, BInt ns ->
        let both =
          List.combine (Array.to_list ms) (Array.to_list ns)
        in
        let ite = List.map (fun (m, n) -> Bdd.ite b m n) both in
        BInt (Array.of_list ite)
    | BOption (tag1, m), BOption (tag2, n) ->
        let tag = Bdd.ite b tag1 tag2 in
        BOption (tag, ite b m n)
    | BTuple ms, BTuple ns ->
        let both = List.combine ms ns in
        let ite = List.map (fun (m, n) -> ite b m n) both in
        BTuple ite
    | _ -> failwith "internal error (ite)"

  let rec eq (x: t) (y: t) : t =
    let rec aux x y : Bdd.vt =
      match (x, y) with
      | BBool b1, BBool b2 -> Bdd.eq b1 b2
      | BInt bs1, BInt bs2 ->
          let both =
            List.combine (Array.to_list bs1) (Array.to_list bs2)
          in
          List.fold_left
            (fun acc (b1, b2) -> Bdd.dand acc (Bdd.eq b1 b2))
            (Bdd.dtrue B.mgr) both
      | BOption (tag1, b1), BOption (tag2, b2) ->
          let tags = Bdd.eq tag1 tag2 in
          let values = aux b1 b2 in
          Bdd.dand tags values
      | BTuple bs1, BTuple bs2 ->
          let both = List.combine bs1 bs2 in
          List.fold_left
            (fun acc (b1, b2) -> Bdd.dand acc (aux b1 b2))
            (Bdd.dtrue B.mgr) both
      | _ -> failwith "internal error (eq)"
    in
    BBool (aux x y)

  let add (x: t) (y: t) : t =
    let aux xs ys =
      let var3 = ref (Bdd.dfalse B.mgr) in
      let var4 = Array.make 32 (Bdd.dfalse B.mgr) in
      for var5 = 0 to Array.length xs - 1 do
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
    | _ -> failwith "internal error (add)"

  (* let sub (x: bdd_value) (y: bdd_value) : bdd_value =
        let aux xs ys =
          let var3 = ref (Bdd.dfalse mgr) in
          let var4 = Array.make 32 (Bdd.dfalse mgr) in
          for var5 = 0 to Array.length xs - 1 do
            var4.(var5) <- Bdd.xor xs.(var5) ys.(var5) ;
            var4.(var5) <- Bdd.xor var4.(var5) !var3 ;
            let var6 = Bdd.dor xs.(var5) !var3 in
            let var7 = Bdd.dand (Bdd.dnot xs.(var5)) var6 in
            let var6 = Bdd.dand xs.(var5) ys.(var5) in
            let var6 = Bdd.dand var6 !var3 in
            let var6 = Bdd.dor var6 var7 in
            var3 := var6
          done ;
          var4
        in
        match (x, y) with
        | BInt xs, BInt ys -> BInt (aux xs ys)
        | _ -> failwith "internal error (sub)" *)

  let leq (x: t) (y: t) : t =
    let less x y = Bdd.dand (Bdd.dnot x) y in
    let aux xs ys =
      let acc = ref (Bdd.dtrue B.mgr) in
      for i = 0 to Array.length xs - 1 do
        let x = xs.(i) in
        let y = ys.(i) in
        acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y))
      done ;
      !acc
    in
    match (x, y) with
    | BInt xs, BInt ys -> BBool (aux xs ys)
    | _ -> failwith "internal error (leq)"

  let lt (x: t) (y: t) : t =
    match (leq x y, eq x y) with
    | BBool b1, BBool b2 ->
        let b = Bdd.dand b1 (Bdd.dnot b2) in
        BBool b
    | _ -> failwith "internal error (lt)"

  let rec eval (env: t Env.t) (e: exp) : t =
    match e.e with
    | ETy (e1, _) -> eval env e1
    | EVar x -> (
      match Env.lookup_opt env x with
      | None -> failwith "internal error (eval)"
      | Some v -> v )
    | EVal v -> eval_value env v
    | EOp (op, es) -> (
      match (op, es) with
      | And, [e1; e2] -> eval_bool_op2 env Bdd.dand e1 e2
      | Or, [e1; e2] -> eval_bool_op2 env Bdd.dor e1 e2
      | Not, [e1] -> eval_bool_op1 env Bdd.dnot e1
      | UEq, [e1; e2] -> eq (eval env e1) (eval env e2)
      | UAdd, [e1; e2] -> add (eval env e1) (eval env e2)
      | ULess, [e1; e2] -> lt (eval env e1) (eval env e2)
      | ULeq, [e1; e2] -> leq (eval env e1) (eval env e2)
      | USub, [e1; e2] -> failwith "subtraction not implemented"
      | _ -> failwith "internal error (eval)" )
    | EIf (e1, e2, e3) -> (
        let v1 = eval env e1 in
        let v2 = eval env e2 in
        let v3 = eval env e3 in
        match v1 with
        | BBool b -> ite b v2 v3
        | _ -> failwith "internal error (eval)" )
    | ELet (x, e1, e2) ->
        let v1 = eval env e1 in
        eval (Env.update env x v1) e2
    | ETuple es ->
        let vs = List.map (eval env) es in
        BTuple vs
    | ESome e -> BOption (Bdd.dtrue B.mgr, eval env e)
    | EMatch (e1, brances) -> failwith ""
    | EFun _ | EApp _ -> failwith ""

  and eval_bool_op1 env f e1 =
    let v1 = eval env e1 in
    match v1 with
    | BBool b1 -> BBool (f b1)
    | _ -> failwith "internal error (eval)"

  and eval_bool_op2 env f e1 e2 =
    let v1 = eval env e1 in
    let v2 = eval env e2 in
    match (v1, v2) with
    | BBool b1, BBool b2 -> BBool (f b1 b2)
    | _ -> failwith "internal error (eval)"

  and eval_value env (v: value) =
    match v.v with
    | VBool b -> BBool (bdd_of_bool b)
    | VUInt32 i ->
        let bs =
          Array.init 32 (fun j ->
              let bit = B.get_bit i j in
              bdd_of_bool bit )
        in
        BInt bs
    | VOption None ->
        let ty =
          match get_inner_type (oget v.vty) with
          | TOption ty -> ty
          | _ -> failwith "internal error (eval_value)"
        in
        let dv = BddMap.default_value ty in
        BOption (Bdd.dfalse B.mgr, eval_value env dv)
    | VOption (Some v) -> BOption (Bdd.dtrue B.mgr, eval_value env v)
    | VTuple vs -> BTuple (List.map (eval_value env) vs)
    | VMap _ | VClosure _ -> failwith "internal error (eval_value)"
end

let default_value = BddMap.default_value
