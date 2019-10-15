open Cudd
open Syntax
open Nv_datastructures
open Nv_utils
open Nv_utils.OCamlUtils
open Batteries

module B = BddUtils

type t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BTuple of t list
  | BOption of Bdd.vt * t

let bdd_of_bool b = if b then Bdd.dtrue B.mgr else Bdd.dfalse B.mgr

let wrap_mtbdd bdd =
  let tru = Mtbdd.cst B.mgr B.tbl_bool true in
  let fal = Mtbdd.cst B.mgr B.tbl_bool false in
  Mtbdd.ite bdd tru fal

let create_value (ty: ty) : t =
  let rec aux i ty =
    match get_inner_type ty with
    | TUnit -> (BBool (B.ithvar i), i + 1)
    | TBool -> (BBool (B.ithvar i), i + 1)
    | TInt size ->
      (BInt (Array.init size (fun j -> B.ithvar (i + j))), i + size)
    | TNode ->
      aux i (TInt 32)
    | TEdge ->
      aux i (TTuple [TNode; TNode])
    | TTuple ts ->
      let bs, idx =
        List.fold_left
          (fun (ls, idx) t ->
             let v, i = aux idx t in
             (v :: ls, i) )
          ([], i) ts
      in
      (BTuple (List.rev bs), idx)
    | TRecord map ->
      aux i (TTuple (RecordUtils.get_record_entries map))
    | TOption ty ->
      let v, idx = aux (i + 1) ty in
      (BOption (B.ithvar i, v), idx)
    | TSubset (ty, _) ->
      aux i ty
    | TArrow _ | QVar _ | TVar _ | TMap _ ->
      failwith "internal error (create_value)"
  in
  let ret, _ = aux 0 ty in
  ret

let rec ite (b: Bdd.vt) (x: t) (y: t) : t =
  match (x, y) with
  | BBool m, BBool n -> BBool (Bdd.ite b m n)
  | BInt ms, BInt ns ->
    BInt (Array.map2 (fun m n -> Bdd.ite b m n) ms ns)
  | BOption (tag1, m), BOption (tag2, n) ->
    let tag = Bdd.ite b tag1 tag2 in
    BOption (tag, ite b m n)
  | BTuple ms, BTuple ns ->
    let ite = List.map2 (fun m n -> ite b m n) ms ns in
    BTuple ite
  | _ -> failwith "internal error (ite)"

let rec eq (x: t) (y: t) : t =
  let rec aux x y : Bdd.vt =
    match (x, y) with
    | BBool b1, BBool b2 -> Bdd.eq b1 b2
    | BInt bs1, BInt bs2 ->
      Array.fold_lefti (fun acc i b1 ->
          Bdd.dand acc (Bdd.eq b1 bs2.(i))) (Bdd.dtrue B.mgr) bs1
    | BOption (tag1, b1), BOption (tag2, b2) ->
      let tags = Bdd.eq tag1 tag2 in
      let values = aux b1 b2 in
      Bdd.dand tags values
    | BTuple bs1, BTuple bs2 ->
      List.fold_left2 (fun acc b1 b2 ->
          Bdd.dand acc (aux b1 b2)) (Bdd.dtrue B.mgr) bs1 bs2
    | _ -> failwith "internal error (eq)"
  in
  BBool (aux x y)

let add (x: t) (y: t) : t =
  let aux xs ys =
    (* assert ((Array.length xs) = (Array.length ys)); *)
    let var3 = ref (Bdd.dfalse B.mgr) in
    let var4 = Array.make (Array.length xs) (Bdd.dfalse B.mgr) in
    let lenxs = Array.length xs in
    for var5 = 0 to lenxs - 1 do
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

let leq (x: t) (y: t) : t =
  let less x y = Bdd.dand (Bdd.dnot x) y in
  let aux xs ys =
    assert ((Array.length xs) = (Array.length ys));
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
      | Eq, [e1; e2] -> eq (eval env e1) (eval env e2)
      | UAdd _, [e1; e2] -> add (eval env e1) (eval env e2)
      | ULess _, [e1; e2] -> lt (eval env e1) (eval env e2)
      | ULeq _, [e1; e2] -> leq (eval env e1) (eval env e2)
      | USub _, [_; _] -> failwith "subtraction not implemented"
      | NLess, [e1; e2] -> lt (eval env e1) (eval env e2)
      | NLeq, [e1; e2] -> leq (eval env e1) (eval env e2)
      | _ -> failwith "unimplemented" )
  | EIf (e1, e2, e3) -> (
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      let v3 = eval env e3 in
      match v1 with
      | BBool b -> ite b v2 v3
      | _ -> failwith "internal error (eval)" )
  | ELet (x, e1, e2) ->
    (* Printf.printf "ELet e1: %s\n" (show_exp ~show_meta:false e1); *)
    let v1 = eval env e1 in
    eval (Env.update env x v1) e2
  | ETuple es ->
    let vs = List.map (eval env) es in
    BTuple vs
  | ESome e -> BOption (Bdd.dtrue B.mgr, eval env e)
  | EMatch (e1, branches) -> (
      let bddf = eval env e1 in
      let ((p,e), bs) = popBranch branches in
      let env, _ = eval_branch env bddf p in
      let x = eval env e in
      let _, x =
        foldBranches (fun (p,e) (env, x) ->
            let env, cond = eval_branch env bddf p in
            (env, ite cond (eval env e) x))
          (env, x) bs
      in
      x )
  | EFun _ | EApp _ | ERecord _ | EProject _ -> failwith "internal error (eval)"

and eval_branch env bddf p : t Env.t * Bdd.vt =
  match (p, bddf) with
  | PWild, _ -> (env, Bdd.dtrue B.mgr)
  | PVar v, _ -> (Env.update env v bddf, Bdd.dtrue B.mgr)
  | PBool true, BBool bdd -> (env, bdd)
  | PBool false, BBool bdd -> (env, Bdd.dnot bdd)
  | PInt i, BInt bi ->
    (* TODO: I'm pretty sure this works, but not entirely. *)
    if Integer.size i <> Array.length bi then
      (env, Bdd.dfalse B.mgr)
    else
      let cond = ref (Bdd.dtrue B.mgr) in
      for j = 0 to Integer.size i - 1 do
        let b = B.get_bit i j in
        let bdd = if b then bi.(j) else Bdd.dnot bi.(j) in
        cond := Bdd.dand !cond bdd
      done ;
      (env, !cond)
  | PTuple ps, BTuple bs ->
    List.fold_left2
      (fun (env, pred) p b ->
         let env', pred' = eval_branch env b p in
         (env', Bdd.dand pred pred') )
      (env, Bdd.dtrue B.mgr) ps bs
  | POption None, BOption (tag, _) -> (env, Bdd.dnot tag)
  | POption (Some p), BOption (tag, bo) ->
    let env, cond = eval_branch env bo p in
    (env, Bdd.dand tag cond)
  | _ -> failwith "internal error (eval_branch)"

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
  | VUnit -> BBool (bdd_of_bool true) (* Encode as boolean *)
  | VBool b -> BBool (bdd_of_bool b)
  | VInt i ->
    let bs =
      Array.init (Integer.size i) (fun j ->
          let bit = B.get_bit i j in
          bdd_of_bool bit )
    in
    BInt bs
  | VNode n ->
    eval_value env (vint (Integer.create ~size:32 ~value:n))
  | VEdge (n1, n2) ->
    eval_value env (vtuple [vnode n1; vnode n2])
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
  | VMap _ | VClosure _ | VRecord _ -> failwith "internal error (eval_value)"
