open Cudd
open Syntax
open Nv_datastructures
open Nv_utils
open Nv_utils.OCamlUtils
open Batteries
open BddMap
module B = BddUtils

(** ** Type of values computed*)
type t =
  | BBool of Bdd.vt (* Boolean BDD *)
  | BInt of Bdd.vt array (* Integer as an array of booleans *)
  | BOption of Bdd.vt * t (* Option of BDD *)
  | Tuple of t list (* Tuple of elements, not necessary BDDs *)
  | BMap of BddMap.t (* MTBDD map, for now leafs are values *)
  | Value of Syntax.value

(* Conventional NV value *)

let rec print (x : t) =
  match x with
  | BBool _ -> "BBool"
  | BInt _ -> "BInt"
  | BOption (_, x) -> Printf.sprintf "BOption[%s]" (print x)
  | Tuple xs -> Collections.printList print xs "[" ";" "]"
  | BMap _ -> "BMap"
  | Value _ -> "Value"
;;

let rec equal_t x y =
  match x, y with
  | BBool b1, BBool b2 -> Bdd.is_equal b1 b2
  | BInt i1, BInt i2 -> Array.for_all2 Bdd.is_equal i1 i2
  | BOption (t1, x), BOption (t2, y) -> Bdd.is_equal t1 t2 && equal_t x y
  | Tuple ts1, Tuple ts2 -> List.for_all2 equal_t ts1 ts2
  | BMap m1, BMap m2 -> BddMap.equal m1 m2
  | Value v1, Value v2 -> equal_values ~cmp_meta:false v1 v2
  | _, _ -> false
;;

(* MTBDD table used for match expressions *)
let tbl_match
    : ('a Env.t * Cudd.Man.v Cudd.Bdd.t option) option Cudd.Mtbdd.table
  =
  Mtbdd.make_table
    ~hash:(fun v ->
      match v with
      | None -> 0
      | Some (env, c) -> 1 + Env.hash env + Hashtbl.hash c)
    ~equal:(fun v1 v2 ->
      match v1, v2 with
      | None, None -> true
      | None, _ | _, None -> false
      | Some (env1, c1), Some (env2, c2) ->
        Env.equal equal_t env1 env2
        &&
        (match c1, c2 with
        | None, None -> true
        | None, _ | _, None -> false
        | Some b1, Some b2 -> Bdd.is_equal b1 b2))
;;

let bdd_of_bool b = if b then Bdd.dtrue B.mgr else Bdd.dfalse B.mgr

(* given a BDD converts it to a MTBDD*)
let wrap_mtbdd bdd =
  let tru = Mtbdd.cst B.mgr B.tbl_bool true in
  let fal = Mtbdd.cst B.mgr B.tbl_bool false in
  Mtbdd.ite bdd tru fal
;;

(* given a boolean MTBDD converts it to a BDD*)
let bdd_of_mtbdd (map : bool Cudd.Mtbdd.unique Cudd.Vdd.t) =
  Mtbdd.guard_of_leaf B.tbl_bool map true
;;

(* Value mtbdd to bool mtbdd*)
let value_mtbdd_bool_mtbdd (map : value Cudd.Mtbdd.unique Cudd.Vdd.t) =
  Mapleaf.mapleaf1
    (fun v ->
      match (Mtbdd.get v).v with
      | VBool b -> b |> Mtbdd.unique B.tbl_bool
      | _ -> failwith "not a bool mtbdd")
    map
;;

(* Given a type creates a BDD representing all possible values of that type*)
let create_value (ty : ty) : t =
  let rec aux i ty =
    match get_inner_type ty with
    | TUnit -> BBool (B.ithvar i), i + 1
    | TBool -> BBool (B.ithvar i), i + 1
    | TInt size -> BInt (Array.init size (fun j -> B.ithvar (i + j))), i + size
    | TNode -> aux i (TInt tnode_sz)
    | TEdge -> aux i (TTuple [TNode; TNode])
    | TTuple ts ->
      let bs, idx =
        List.fold_left
          (fun (ls, idx) t ->
            let v, i = aux idx t in
            v :: ls, i)
          ([], i)
          ts
      in
      Tuple (List.rev bs), idx
    | TRecord map -> aux i (TTuple (RecordUtils.get_record_entries map))
    | TOption ty ->
      let v, idx = aux (i + 1) ty in
      BOption (B.ithvar i, v), idx
    | TArrow _ | QVar _ | TVar _ | TMap _ ->
      failwith
        (Printf.sprintf
           "internal error (create_value) type:%s\n"
           (Printing.ty_to_string (get_inner_type ty)))
  in
  let ret, _ = aux 0 ty in
  ret
;;

(* Constrains the MTBDD table variables by the given BDD *)
let constrain_bdd (x : t) (typ : Syntax.ty) : Bdd.vt =
  let rec aux x idx ty =
    match x, get_inner_type ty with
    | BBool b, TBool ->
      let var = B.ithvar idx in
      Bdd.eq var b, idx + 1
    | BInt xs, TInt size ->
      ( Array.fold_lefti
          (fun acc i b1 -> Bdd.dand acc (Bdd.eq b1 (B.ithvar (i + idx))))
          (Bdd.dtrue B.mgr)
          xs
      , idx + size )
    | x, TNode -> aux x idx (TInt tnode_sz)
    | x, TEdge -> aux x idx (TTuple [TNode; TNode])
    | Tuple xs, TTuple ts ->
      List.fold_left2
        (fun (bdd_acc, idx) v ty ->
          let bdd, i = aux v idx ty in
          Bdd.dand bdd_acc bdd, i)
        (Bdd.dtrue B.mgr, idx)
        xs
        ts
    | x, TRecord map -> aux x idx (TTuple (RecordUtils.get_record_entries map))
    | BOption (tag, x), TOption ty ->
      let t = Bdd.eq tag (B.ithvar idx) in
      let v, idx = aux x (idx + 1) ty in
      Bdd.dand t v, idx
    | _, _ -> failwith (Printf.sprintf "internal error (constrain_bdd)\n")
  in
  let ret, _ = aux x 0 typ in
  ret
;;

(** Is x a BDD value?*)
let rec isBdd (x : t) =
  match x with
  | BBool _ | BInt _ -> true
  | BOption (_, b) -> isBdd b
  | BMap _ | Tuple _ | Value _ -> false
;;

(** Lifts an NV value to a BDD*)
let rec eval_value (v : value) : t =
  match v.v with
  | VUnit -> BBool (bdd_of_bool true) (* Encode as boolean *)
  | VBool b -> BBool (bdd_of_bool b)
  | VInt i ->
    let bs =
      Array.init (Integer.size i) (fun j ->
          let bit = B.get_bit i j in
          bdd_of_bool bit)
    in
    BInt bs
  | VNode n -> eval_value (vint (Integer.create ~size:tnode_sz ~value:n))
  | VEdge (n1, n2) -> eval_value (vtuple [vnode n1; vnode n2])
  | VOption None ->
    let ty =
      match get_inner_type (oget v.vty) with
      | TOption ty -> ty
      | _ -> failwith "internal error (eval_value)"
    in
    let dv = BddMap.default_value ty in
    BOption (Bdd.dfalse B.mgr, eval_value dv)
  | VOption (Some v) -> BOption (Bdd.dtrue B.mgr, eval_value v)
  | VTuple vs -> Tuple (List.map eval_value vs)
  | VMap _ | VClosure _ | VRecord _ -> failwith "internal error (eval_value)"
;;

let eval_value_id (v : t) : t =
  match v with
  | Value v -> eval_value v
  | _ -> v
;;

(** if-then-else between BDDs*)
let rec ite (b : Bdd.vt) (x : t) (y : t) : t =
  match x, y with
  | BBool m, BBool n -> BBool (Bdd.ite b m n)
  | BInt ms, BInt ns -> BInt (Array.map2 (fun m n -> Bdd.ite b m n) ms ns)
  | BOption (tag1, m), BOption (tag2, n) ->
    let tag = Bdd.ite b tag1 tag2 in
    BOption (tag, ite b m n)
  | Tuple ms, Tuple ns ->
    let ite = List.map2 (fun m n -> ite b m n) ms ns in
    Tuple ite
  | _ -> failwith "internal error (ite)"
;;

(** equality between BDDs*)
let rec eqBdd x y : Bdd.vt =
  match x, y with
  | BBool b1, BBool b2 -> Bdd.eq b1 b2
  | BInt bs1, BInt bs2 ->
    Array.fold_lefti
      (fun acc i b1 -> Bdd.dand acc (Bdd.eq b1 bs2.(i)))
      (Bdd.dtrue B.mgr)
      bs1
  | BOption (tag1, b1), BOption (tag2, b2) ->
    let tags = Bdd.eq tag1 tag2 in
    let values = eqBdd b1 b2 in
    Bdd.dand tags values
  | Value _, Value _ -> failwith "handled elsewhere"
  | Tuple _, Tuple _ -> failwith "handled elsewhere"
  | _ -> failwith "internal error (eq)"
;;

(** Equality between maps (and values)*)
let eqMap x y : Bdd.vt =
  match x, y with
  | BMap m1, BMap m2 ->
    Mapleaf.mapleaf2
      (fun v1 v2 ->
        equal_values ~cmp_meta:false (Mtbdd.get v1) (Mtbdd.get v2)
        |> Mtbdd.unique B.tbl_bool)
      (fst m1)
      (fst m2)
    |> bdd_of_mtbdd
  | BMap m, Value v | Value v, BMap m ->
    Mapleaf.mapleaf1
      (fun vm ->
        equal_values ~cmp_meta:false (Mtbdd.get vm) v |> Mtbdd.unique B.tbl_bool)
      (fst m)
    |> bdd_of_mtbdd
  | _, _ -> failwith "equality between maps and values only"
;;

let isMap x =
  match x with
  | BMap _ -> true
  | BBool _ | BInt _ | BOption _ | Tuple _ | Value _ -> false
;;

(** Equality between [t] values*)
let rec eq (x : t) (y : t) : t =
  if isBdd x || isBdd y
  then (*lift to bdd *)
    BBool (eqBdd (eval_value_id x) (eval_value_id y))
  else if isMap x || isMap y
  then (*lift to mtbdd*)
    BBool (eqMap x y)
  else (
    match x, y with
    | Value v1, Value v2 ->
      Value
        (if equal_values ~cmp_meta:false v1 v2 then vbool true else vbool false)
    | Tuple bs1, Tuple bs2 -> eq_list bs1 bs2 (Value (vbool true))
    | BOption (tag1, b1), BOption (tag2, b2) ->
      let tag_eq = Bdd.eq tag1 tag2 in
      if Bdd.is_true tag_eq
      then eq b1 b2
      else if Bdd.is_false tag_eq
      then Value (vbool false)
      else failwith "this case cannot happen I think.."
    | Tuple bs, Value v | Value v, Tuple bs ->
      (match v.v with
      | VTuple vs ->
        eq_list bs (List.map (fun v -> Value v) vs) (Value (vbool true))
      | VEdge (n1, n2) ->
        eq_list bs [Value (vnode n1); Value (vnode n2)] (Value (vbool true))
      | _ -> failwith "mistyped equality")
    | _, _ -> failwith "impossible cases")

and eq_list xs ys acc =
  match xs, ys with
  | [], [] -> acc
  | x :: xs, y :: ys ->
    (match eq x y with
    | Value v ->
      (match v.v with
      | VBool true -> eq_list xs ys acc
      | VBool false -> Value (vbool false)
      | _ -> failwith "mistyped equality check")
    | BBool b ->
      (match acc with
      | Value _ -> eq_list xs ys (BBool b)
      | BBool bacc -> eq_list xs ys (BBool (Bdd.dand b bacc))
      | _ -> failwith "mistyped equality check")
    | _ -> failwith "mistyped equality check")
  | _, _ -> failwith "can only compare tuples of same length"
;;

(** ** BDD Operations*)
let add xs ys =
  let var3 = ref (Bdd.dfalse B.mgr) in
  let var4 = Array.make (Array.length xs) (Bdd.dfalse B.mgr) in
  let lenxs = Array.length xs in
  for var5 = 0 to lenxs - 1 do
    var4.(var5) <- Bdd.xor xs.(var5) ys.(var5);
    var4.(var5) <- Bdd.xor var4.(var5) !var3;
    let var6 = Bdd.dor xs.(var5) ys.(var5) in
    let var6 = Bdd.dand var6 !var3 in
    let var7 = Bdd.dand xs.(var5) ys.(var5) in
    let var7 = Bdd.dor var7 var6 in
    var3 := var7
  done;
  BInt var4
;;

(** Bitwise and operation. Requires that the two integers are of the same size. *)
let uand xs ys =
  BInt (Array.init (Array.length xs) (fun i -> Bdd.dand xs.(i) ys.(i)))
;;

(* Outdated. Compare with add above if uncommenting *)
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

let leq xs ys =
  let less x y = Bdd.dand (Bdd.dnot x) y in
  let acc = ref (Bdd.dtrue B.mgr) in
  Array.iter2
    (fun x y -> acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y)))
    xs
    ys;
  BBool !acc
;;

let lt xs ys =
  match leq xs ys, eq (BInt xs) (BInt ys) with
  | BBool b1, BBool b2 ->
    let b = Bdd.dand b1 (Bdd.dnot b2) in
    BBool b
  | _ -> failwith "internal error (lt)"
;;

(** ** Lifted binary and unary NV operations *)

let eval_int_op2 f f_lifted (x : t) (y : t) : t =
  match x, y with
  | Value v1, Value v2 ->
    (match v1.v, v2.v with
    | VInt n, VInt m -> Value (f n m)
    | _, _ -> failwith "mistyped integer computation")
  | Value v1, BInt b2 ->
    (match eval_value v1 with
    | BInt b1 -> f_lifted b1 b2
    | _ -> failwith "mistyped integer computation")
  | BInt b1, Value v2 ->
    (match eval_value v2 with
    | BInt b2 -> f_lifted b1 b2
    | _ -> failwith "mistyped integer computation")
  | BInt b1, BInt b2 -> f_lifted b1 b2
  | BMap m1, BMap m2 ->
    BMap
      ( Mapleaf.mapleaf2
          (fun v1 v2 ->
            match (Mtbdd.get v1).v, (Mtbdd.get v2).v with
            | VInt n, VInt m -> f n m |> Mtbdd.unique B.tbl
            | _, _ -> failwith "Mistyped integer computation")
          (fst m1)
          (fst m2)
      , snd m1 )
  | BMap m1, Value v2 ->
    BMap
      ( Mapleaf.mapleaf1
          (fun v1 ->
            match (Mtbdd.get v1).v, v2.v with
            | VInt n, VInt m -> f n m |> Mtbdd.unique B.tbl
            | _, _ -> failwith "Mistyped boolean computation")
          (fst m1)
      , snd m1 )
  | Value v2, BMap m1 ->
    BMap
      ( Mapleaf.mapleaf1
          (fun v1 ->
            match v2.v, (Mtbdd.get v1).v with
            | VInt n, VInt m -> f n m |> Mtbdd.unique B.tbl
            | _, _ -> failwith "Mistyped boolean computation")
          (fst m1)
      , snd m1 )
  | BMap _, BInt _ | BInt _, BMap _ ->
    failwith "currently not lifting operations between maps and predicate key"
  | _ -> failwith "internal error (eval_int_op2)"
;;

(* Used for matches over maps*)
let eval_branch_mapLift env matches key_ty =
  (* Compute a condition under which we match and a conditional environment*)
  let result =
    Array.fold_left
      (fun acc (k, v) ->
        match v with
        | None -> acc (* not a match*)
        | Some (matchEnv, c) ->
          (* if there is a match with env under condition c*)
          let cond =
            match c with
            | None -> k (*if there is no condition then just use k*)
            | Some c -> Bdd.dand k c
            (*otherwise their conjunction*)
          in
          (match acc with
          | None ->
            (* If there is no other match*)
            let newEnv =
              Env.map matchEnv (fun v ->
                  match v with
                  | Value v -> BMap (BddMap.create key_ty v)
                  | _ -> failwith "Must be a value")
            in
            Some (newEnv, Some cond)
          | Some (accEnv, accC) ->
            (* Combine the current match with existing ones*)
            (* The environment is altered to return the current values
                for keys that correspond to this match and
                the condition is "extended" via a bdd-or to denote a match*)
            let newEnv =
              Env.combineValues
                (fun vacc v ->
                  match vacc, v with
                  | BMap m, Value v ->
                    (* For keys that satisfy the current condition
                        return v otherwise return whatever was in them map*)
                    BMap
                      ( Mapleaf.mapleaf2
                          (fun b vcur ->
                            (if Mtbdd.get b then v else Mtbdd.get vcur)
                            |> Mtbdd.unique B.tbl)
                          (wrap_mtbdd cond)
                          (fst m)
                      , snd m )
                  | _, _ -> failwith "Invalid combination")
                accEnv
                matchEnv
            in
            let newCond =
              match accC with
              | None -> cond
              | Some accC -> Bdd.dor accC cond
            in
            Some (newEnv, Some newCond)))
      None
      matches
  in
  (* need to add previous environment*)
  match result with
  | None -> None
  | Some (matchEnv, c) -> Some (Env.updates env matchEnv, c)
;;

let rec t_to_bdd (x : t) =
  match x with
  | BInt _ | BBool _ -> x
  | BOption (tag, x) -> BOption (tag, t_to_bdd x)
  | Tuple ls -> Tuple (List.map t_to_bdd ls)
  | Value v -> eval_value v
  | BMap _ -> failwith "failing for now"
;;

let eval_tget lo hi x =
  let eval_tget_v lo hi v =
    match v.v with
    | VTuple elts ->
      if lo = hi
      then List.nth elts lo
      else vtuple (elts |> BatList.drop lo |> BatList.take (hi - lo + 1))
    | _ -> failwith "expected a tuple"
  in
  match x with
  | Value v -> Value (eval_tget_v lo hi v)
  | Tuple elts ->
    if lo = hi
    then List.nth elts lo
    else Tuple (elts |> BatList.drop lo |> BatList.take (hi - lo + 1))
  | BMap m ->
    BMap
      ( Mapleaf.mapleaf1
          (fun v -> eval_tget_v lo hi (Mtbdd.get v) |> Mtbdd.unique B.tbl)
          (fst m)
      , snd m )
  | _ -> failwith "Impossible"
;;

let eval_tset lo hi xs x =
  match xs, x with
  | Value vs, Value v ->
    (match vs.v with
    | VTuple elts ->
      if lo = hi
      then Value (vtuple (BatList.modify_at lo (fun _ -> v) elts))
      else (
        match v.v with
        | VTuple velts ->
          Value (vtuple (OCamlUtils.replaceSlice lo hi elts velts))
        | _ -> failwith "Bad TSet")
    | _ -> failwith "Expected a tuple")
  | Value vs, x ->
    (match vs.v with
    | VTuple elts ->
      let elts = List.map (fun v -> Value v) elts in
      if lo = hi
      then Tuple (BatList.modify_at lo (fun _ -> x) elts)
      else (
        match x with
        | Tuple newElts -> Tuple (OCamlUtils.replaceSlice lo hi elts newElts)
        (* more cases likely apply but unimportant as this should always be lo=hi*)
        | _ -> failwith "Bad TSet")
    | _ -> failwith "Expected a tuple")
  | Tuple elts, x ->
    if lo = hi
    then Tuple (BatList.modify_at lo (fun _ -> x) elts)
    else (
      match x with
      | Tuple newElts -> Tuple (OCamlUtils.replaceSlice lo hi elts newElts)
      (* more cases likely apply but unimportant as this should always be lo=hi*)
      | _ -> failwith "Bad TSet")
  | BMap m, Value v ->
    BMap
      ( Mapleaf.mapleaf1
          (fun vs ->
            (match (Mtbdd.get vs).v with
            | VTuple elts ->
              if lo = hi
              then vtuple (BatList.modify_at lo (fun _ -> v) elts)
              else (
                match v.v with
                | VTuple velts ->
                  vtuple (OCamlUtils.replaceSlice lo hi elts velts)
                | _ -> failwith "Bad TSet")
            | _ -> failwith "Expected a tuple")
            |> Mtbdd.unique B.tbl)
          (fst m)
      , snd m )
  | _ -> failwith "Impossible"
;;

let rec eval (env : t Env.t) (e : exp) : t =
  match e.e with
  | ETy (e1, _) -> eval env e1
  | EVar x ->
    (match Env.lookup_opt env x with
    | None -> failwith "internal error (eval - lookup failed)"
    | Some v -> v)
  | EVal v -> Value v
  | EOp (op, es) ->
    begin
      match op, es with
      | And, [e1; e2] -> eval_bool_op2 env ( && ) Bdd.dand e1 e2
      | Or, [e1; e2] -> eval_bool_op2 env ( || ) Bdd.dor e1 e2
      | Not, [e1] -> eval_bool_op1 env not Bdd.dnot e1
      | Eq, [e1; e2] -> eq (eval env e1) (eval env e2)
      | UAdd _, [e1; e2] ->
        eval_int_op2
          (fun i1 i2 -> vint (Integer.add i1 i2))
          add
          (eval env e1)
          (eval env e2)
      | ULess _, [e1; e2] ->
        eval_int_op2
          (fun i1 i2 -> vbool (Integer.lt i1 i2))
          lt
          (eval env e1)
          (eval env e2)
      | UAnd _, [e1; e2] ->
        eval_int_op2
          (fun i1 i2 -> vint (Integer.uand i1 i2))
          uand
          (eval env e1)
          (eval env e2)
      | ULeq _, [e1; e2] ->
        eval_int_op2
          (fun i1 i2 -> vbool (Integer.leq i1 i2))
          leq
          (eval env e1)
          (eval env e2)
      | NLess, [e1; e2] ->
        eval_int_op2
          (fun i1 i2 -> vbool (Integer.lt i1 i2))
          lt
          (eval env e1)
          (eval env e2)
      | NLeq, [e1; e2] ->
        eval_int_op2
          (fun i1 i2 -> vbool (Integer.leq i1 i2))
          leq
          (eval env e1)
          (eval env e2)
      | TGet (_, lo, hi), [e1] -> eval_tget lo hi (eval env e1)
      | MGet, [e1; e2] ->
        let v1 = eval env e1 in
        let v2 = eval env e2 in
        let m =
          match v1 with
          | BMap m -> m
          | Value v ->
            (match v.v with
            | VMap m -> m
            | _ -> failwith "mistyped")
          | _ -> failwith "mistyped evaluation"
        in
        (match v2 with
        | Value v -> Value (BddMap.find m v)
        | _ ->
          let k = t_to_bdd v2 in
          let newm = Mtbdd.constrain (fst m) (constrain_bdd k (snd m)) in
          BMap (newm, snd m))
      | USub _, [_; _] -> failwith "subtraction not implemented"
      | _ -> failwith "Wrong number of arguments to operation"
    end
  | EIf (e1, e2, e3) -> eval_ite env e1 e2 e3
  | ELet (x, e1, e2) ->
    (* Printf.printf "ELet e1: %s\n" (show_exp ~show_meta:false e1); *)
    let v1 = eval env e1 in
    eval (Env.update env x v1) e2
  | ETuple es ->
    let vs = List.map (eval env) es in
    Tuple vs
  | ESome e ->
    (match eval env e with
    | Value v -> Value (voption (Some v))
    | BMap m ->
      BMap
        ( Mapleaf.mapleaf1
            (fun v -> voption (Some (Mtbdd.get v)) |> Mtbdd.unique B.tbl)
            (fst m)
        , snd m )
    (* NOTE: Decided to push the option through a map, it makes writing functions like eval_ite_bdd_guard much easier... *)
    | b -> BOption (Bdd.dtrue B.mgr, b))
  | EMatch (e1, branches) ->
    let v1 = eval env e1 in
    eval_matches
      env
      (oget e1.ety)
      v1
      branches
      (Value (default_value (oget e.ety)))
  | EFun _ | EApp _ | ERecord _ | EProject _ -> failwith "internal error (eval)"

and eval_matches env key_ty v1 branches default =
  if isEmptyBranch branches
  then default
  else (
    let (p, e), bs = popBranch branches in
    (* Printf.printf "branch: %s\n\n" (Printing.pattern_to_string p);
     * Printf.printf "guard: %s\n\n" (print v1);
     * Printf.printf "expr: %s\n\n" (Printing.exp_to_string e); *)
    match eval_branch env v1 p with
    | None ->
      (* no match - go to next branch*)
      eval_matches env key_ty v1 bs default
    | Some (newEnv, None) ->
      (*conditionless match - stop looking at the next branches*)
      eval newEnv e
    | Some (newEnv, Some cond) ->
      (*match under a BDD-condition*)
      (* if the condition is met then evaluate the expression
       * otherwise go to next branch*)
      eval_ite_bdd_guard
        key_ty
        cond
        (eval newEnv e)
        (eval_matches env key_ty v1 bs default))

and eval_branch env (g : t) p =
  match p, g with
  | PWild, _ -> Some (env, None)
  | PVar x, _ -> Some (Env.update env x g, None)
  | PBool b, Value v ->
    (match v.v with
    | VBool bv when bv = b -> Some (env, None)
    | _ -> None)
  | PBool b, BBool bv ->
    if b then Some (env, Some bv) else Some (env, Some (Bdd.dnot bv))
  | PBool b, BMap m ->
    let cond =
      Mapleaf.mapleaf1
        (fun vm ->
          (match (Mtbdd.get vm).v with
          | VBool bv when bv = b -> true
          | _ -> false)
          |> Mtbdd.unique B.tbl_bool)
        (fst m)
      |> bdd_of_mtbdd
    in
    Some (env, Some cond)
  | PInt pi, Value v ->
    (match v.v with
    | VInt vi when Integer.equal pi vi -> Some (env, None)
    | _ -> None)
  | PInt pi, BInt bi ->
    if Integer.size pi <> Array.length bi
    then failwith "Likely failure of type checking."
    else (
      let cond = ref (Bdd.dtrue B.mgr) in
      for j = 0 to Integer.size pi - 1 do
        let b = B.get_bit pi j in
        let bdd = if b then bi.(j) else Bdd.dnot bi.(j) in
        cond := Bdd.dand !cond bdd
      done;
      Some (env, Some !cond))
  | PInt pi, BMap m ->
    let cond =
      Mapleaf.mapleaf1
        (fun vm ->
          (match (Mtbdd.get vm).v with
          | VInt vi when Integer.equal pi vi -> true
          | _ -> false)
          |> Mtbdd.unique B.tbl_bool)
        (fst m)
      |> bdd_of_mtbdd
    in
    Some (env, Some cond)
  | PNode pi, Value v ->
    (match v.v with
    | VNode vi when pi = vi -> Some (env, None)
    | _ -> None)
  | PNode pi, BInt bi ->
    if Syntax.tnode_sz <> Array.length bi
    then failwith "Likely failure of type checking."
    else (
      let pi = Integer.create ~value:pi ~size:tnode_sz in
      let cond = ref (Bdd.dtrue B.mgr) in
      for j = 0 to tnode_sz - 1 do
        let b = B.get_bit pi j in
        let bdd = if b then bi.(j) else Bdd.dnot bi.(j) in
        cond := Bdd.dand !cond bdd
      done;
      Some (env, Some !cond))
  | PNode pi, BMap m ->
    let cond =
      Mapleaf.mapleaf1
        (fun vm ->
          (match (Mtbdd.get vm).v with
          | VNode vi when pi = vi -> true
          | _ -> false)
          |> Mtbdd.unique B.tbl_bool)
        (fst m)
      |> bdd_of_mtbdd
    in
    Some (env, Some cond)
  | POption None, Value v ->
    (match v.v with
    | VOption None -> Some (env, None)
    | _ -> None)
  | POption None, BOption (tag, _) ->
    if Bdd.is_false tag
    then (* if tag is a false constant*)
      Some (env, None)
    else if Bdd.is_true tag
    then (*if tag is a true constant*)
      None
    else (*if non-constant*)
      Some (env, Some (Bdd.dnot tag))
  | POption None, BMap m ->
    let cond =
      Mapleaf.mapleaf1
        (fun vm ->
          (match (Mtbdd.get vm).v with
          | VOption None -> true
          | _ -> false)
          |> Mtbdd.unique B.tbl_bool)
        (fst m)
      |> bdd_of_mtbdd
    in
    Some (env, Some cond)
  | POption (Some p), Value v ->
    (match v.v with
    | VOption (Some v1) ->
      (match eval_branch env (Value v1) p with
      | None -> None
      | Some (env, None) -> Some (env, None)
      | _ -> failwith "should not occur")
    | _ -> None)
  | POption (Some p), BMap m ->
    let matches =
      Mtbdd.guardleafs
        (Mapleaf.mapleaf1
           (fun vm ->
             eval_branch Env.empty (Value (Mtbdd.get vm)) (POption (Some p))
             |> Mtbdd.unique tbl_match)
           (fst m))
    in
    eval_branch_mapLift env matches (snd m)
  | POption (Some p), BOption (tag, v) ->
    if Bdd.is_false tag
    then (* if tag is a false constant*)
      None
    else if Bdd.is_true tag
    then (
      (*if tag is a true constant*)
      match eval_branch env v p with
      (*check that inner-pattern matches*)
      | None -> None
      | Some res -> Some res)
    else (
      (*if non-constant*)
      match eval_branch env v p with
      (*check that inner-pattern matches*)
      | None -> None
      | Some (env, None) -> Some (env, Some tag)
      | Some (env, Some cond) ->
        (* if inner pattern matches under some condition /\ this cond to the tag*)
        Some (env, Some (Bdd.dand tag cond)))
  | PTuple ps, Value v ->
    (match v.v with
    | VTuple vs ->
      (match ps, vs with
      | [], [] -> Some (env, None)
      | p :: ps, v :: vs ->
        (match eval_branch env (Value v) p with
        | None -> None
        | Some (env, None) ->
          (* condition must be empty since these are normal values*)
          eval_branch env (Value (vtuple vs)) (PTuple ps)
        | _ -> failwith "impossible")
      | _, _ -> failwith "mistyped pattern matching")
    | _ -> failwith "Mistyped pattern matching")
  | PTuple ps, Tuple bs ->
    (match ps, bs with
    | [], [] -> Some (env, None)
    | p :: ps, b :: bs ->
      (match eval_branch env b p with
      | None -> None
      | Some (env, c) ->
        (match eval_branch env (Tuple bs) (PTuple ps) with
        | None -> None
        | Some (env, crec) ->
          let cond =
            match c, crec with
            | None, _ -> crec
            | _, None -> c
            | Some c, Some crec -> Some (Bdd.dand c crec)
          in
          Some (env, cond)))
    | _, _ -> failwith "Mistyped pattern matching")
  | PTuple ps, BMap m ->
    (* Every leaf will have a value denoting whether it matched
          (None/Some), the env the match generates, as well as any
          conditions under which the match happens. For every leaf
          that there was a match and any conditions under which the
          match is valid, we bdd-and the keys that lead to the leaf
          and the conditions and use them to return the right value
          from the env. *)
    (*NOTE: will their be conditions under each match holds? These are concrete
    values, maybe this can be simplified. *)
    let matches =
      Mtbdd.guardleafs
        (Mapleaf.mapleaf1
           (fun vm ->
             eval_branch Env.empty (Value (Mtbdd.get vm)) (PTuple ps)
             |> Mtbdd.unique tbl_match)
           (fst m))
    in
    eval_branch_mapLift env matches (snd m)

(* | _ ->
 *   failwith "unknown error" *)

(* Example: m[k]: int * map[int,bool] * int match m[k] with | (0,_,0) -> None |
   (1, c, 1) -> Some (c[1]) | (_, c, _) -> Some (c[0])
   the above matches (1,1,1) and (1,2,1), assigning a different value to
   c. Need to treat that in the env = {c |-> Map (Mtbdd...)}*)
and eval_bool_op1 env f f_lifted e1 =
  let v1 = eval env e1 in
  match v1 with
  | BBool b1 -> BBool (f_lifted b1)
  | Value v1 ->
    (match v1.v with
    | VBool b -> Value (vbool (f b))
    | _ -> failwith "mistyped boolean computation")
  | BMap m1 ->
    BMap
      ( Mapleaf.mapleaf1
          (fun v1 ->
            match (Mtbdd.get v1).v with
            | VBool b1 -> vbool (f b1) |> Mtbdd.unique B.tbl
            | _ -> failwith "Mistyped boolean computation")
          (fst m1)
      , snd m1 )
  | _ -> failwith "internal error (eval_bool_op1)"

and eval_bool_op2 env f f_lifted e1 e2 =
  let v1 = eval env e1 in
  let v2 = eval env e2 in
  match v1, v2 with
  | Value v1, Value v2 ->
    (match v1.v, v2.v with
    | VBool b1, VBool b2 -> Value (vbool (f b1 b2))
    | _, _ -> failwith "mistyped boolean computation")
  | Value v1, BBool b2 ->
    (match eval_value v1 with
    | BBool b1 -> BBool (f_lifted b1 b2)
    | _ -> failwith "mistyped boolean computation")
  | BBool b1, Value v2 ->
    (match eval_value v2 with
    | BBool b2 -> BBool (f_lifted b1 b2)
    | _ -> failwith "mistyped boolean computation")
  | BBool b1, BBool b2 -> BBool (f_lifted b1 b2)
  | BMap m1, BMap m2 ->
    BMap
      ( Mapleaf.mapleaf2
          (fun v1 v2 ->
            match (Mtbdd.get v1).v, (Mtbdd.get v2).v with
            | VBool b1, VBool b2 -> vbool (f b1 b2) |> Mtbdd.unique B.tbl
            | _, _ -> failwith "Mistyped boolean computation")
          (fst m1)
          (fst m2)
      , snd m1 )
  | BMap m1, Value v2 | Value v2, BMap m1 ->
    BMap
      ( Mapleaf.mapleaf1
          (fun v1 ->
            match (Mtbdd.get v1).v, v2.v with
            | VBool b1, VBool b2 -> vbool (f b1 b2) |> Mtbdd.unique B.tbl
            | _, _ -> failwith "Mistyped boolean computation")
          (fst m1)
      , snd m1 )
  | BMap _, BBool _ | BBool _, BMap _ ->
    failwith "currently not lifting operations between maps and predicate key"
  | _ -> failwith "internal error (eval_bool_op2)"

and eval_ite env e1 e2 e3 =
  let g = eval env e1 in
  let g =
    match g with
    | Value _ | BBool _ -> g
    | BMap m ->
      BBool
        (bdd_of_mtbdd
           (Mapleaf.mapleaf1
              (fun v ->
                match (Mtbdd.get v).v with
                | VBool b -> b |> Mtbdd.unique B.tbl_bool
                | _ -> failwith "expected a bool")
              (fst m)))
    | _ -> failwith "mistyped ite guard"
  in
  match g with
  | Value v1 ->
    (match v1.v with
    | VBool b -> if b then eval env e2 else eval env e3
    | _ -> failwith "mistyped ite guard")
  | BBool b -> eval_ite_bdd_guard (oget e1.ety) b (eval env e2) (eval env e3)
  | _ -> failwith "impossible"

(* TODO: this doesn't work if we are trying to combine a BInt and a BMap *)
and eval_ite_bdd_guard key_ty b v1 v2 =
  (* Printf.printf "v1: %s\n" (print v1);
   * Printf.printf "v2: %s\n" (print v2); *)
  match v1, v2 with
  | Value v1, Value v2 ->
    BMap
      ( Mapleaf.mapleaf1
          (fun b -> (if Mtbdd.get b then v1 else v2) |> Mtbdd.unique B.tbl)
          (wrap_mtbdd b)
      , key_ty )
  | BMap m1, BMap m2 ->
    let res =
      User.map_op3
        ~special:(fun bdd1 bdd2 bdd3 ->
          if Vdd.is_cst bdd1
          then Some (if Mtbdd.dval bdd1 then bdd2 else bdd3)
          else None)
        (fun b1 b2 b3 ->
          (if Mtbdd.get b1 then Mtbdd.get b2 else Mtbdd.get b3)
          |> Mtbdd.unique B.tbl)
        (wrap_mtbdd b)
        (fst m1)
        (fst m2)
    in
    BMap (res, snd m1)
  | BMap m1, Value v2 ->
    BMap
      ( Mapleaf.mapleaf2
          (fun b v ->
            (if Mtbdd.get b then Mtbdd.get v else v2) |> Mtbdd.unique B.tbl)
          (wrap_mtbdd b)
          (fst m1)
      , snd m1 )
  | Value v1, BMap m2 ->
    BMap
      ( Mapleaf.mapleaf2
          (fun b v ->
            (if Mtbdd.get b then v1 else Mtbdd.get v) |> Mtbdd.unique B.tbl)
          (wrap_mtbdd b)
          (fst m2)
      , snd m2 )
  | Value v1, b2 when isBdd b2 = true -> ite b (eval_value v1) b2
  | b1, Value v2 when isBdd b1 = true -> ite b b1 (eval_value v2)
  (* | Value v1, BOption (tag, b2) -> (\*b2 is not a BDD, i.e. it's a map because we do not push values inside BOptions, but we push maps*\)
   *   match tag with
   *   | BOption (tag1, b1) ->
   *     BMap (Mapleaf.mapleaf1
   *             (fun b -> (if Mtbdd.get b then v1 else v2)
   *                       |> Mtbdd.unique B.tbl) (wrap_mtbdd b), key_ty)
   *   ite b (eval_value v1) b2
   * | b1, Value v2 when isBdd b1 = true ->
   *   ite b b1 (eval_value v2) *)
  | BMap m1, BBool _ ->
    (* Convert the boolean MTBDD to a BDD and do a BDD.ite operation *)
    ite b (BBool (bdd_of_mtbdd @@ value_mtbdd_bool_mtbdd (fst m1))) v2
  | BBool _, BMap m2 ->
    (* Convert the boolean MTBDD to a BDD and do a BDD.ite operation *)
    ite b v1 (BBool (bdd_of_mtbdd @@ value_mtbdd_bool_mtbdd (fst m2)))
  | Tuple bs1, Tuple bs2 -> Tuple (eval_ite_list key_ty b bs1 bs2)
  | Tuple bs1, Value v2 ->
    (match v2.v with
    | VTuple vs2 ->
      Tuple (eval_ite_list key_ty b bs1 (List.map (fun v -> Value v) vs2))
    | _ -> failwith "expected a tuple of values")
  | Value v1, Tuple bs2 ->
    (match v1.v with
    | VTuple vs1 ->
      Tuple (eval_ite_list key_ty b (List.map (fun v -> Value v) vs1) bs2)
    | _ -> failwith "expected a tuple of values")
  | b1, b2 when isBdd b1 && isBdd b2 -> ite b b1 b2
  | Tuple _, BMap _ | BMap _, Tuple _ ->
    failwith "unsure how to implement this case, leaving out for now"
  | _ -> failwith "unknown error"

and eval_ite_list key_ty b bs1 bs2 =
  match bs1, bs2 with
  | [], [] -> []
  | b1 :: bs1, b2 :: bs2 ->
    eval_ite_bdd_guard key_ty b b1 b2 :: eval_ite_list key_ty b bs1 bs2
  | _ -> failwith "tuples must have equal length - impossible"
;;
