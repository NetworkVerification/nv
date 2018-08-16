open BddUtils
open Cudd
open Syntax
open Unsigned

type t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BTuple of t list
  | BOption of Bdd.vt * t

let bdd_of_bool b = if b then Bdd.dtrue mgr else Bdd.dfalse mgr

let create_value (ty: ty) : t =
  let rec aux i ty =
    match get_inner_type ty with
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

let rec ite (b: Bdd.vt) (x: t) (y: t) : t =
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

let rec eq (x: t) (y: t) : t =
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

let add (x: t) (y: t) : t =
  let aux xs ys =
    let var3 = ref (Bdd.dfalse mgr) in
    let var4 = Array.make 32 (Bdd.dfalse mgr) in
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
  | _ -> Console.error "internal error (add)"

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
    | _ -> Console.error "internal error (sub)" *)

let leq (x: t) (y: t) : t =
  let less x y = Bdd.dand (Bdd.dnot x) y in
  let aux xs ys =
    let acc = ref (Bdd.dtrue mgr) in
    for i = 0 to Array.length xs - 1 do
      let x = xs.(i) in
      let y = ys.(i) in
      acc := Bdd.dor (less x y) (Bdd.dand !acc (Bdd.eq x y))
    done ;
    !acc
  in
  match (x, y) with
  | BInt xs, BInt ys -> BBool (aux xs ys)
  | _ -> Console.error "internal error (leq)"

let lt (x: t) (y: t) : t =
  match (leq x y, eq x y) with
  | BBool b1, BBool b2 ->
      let b = Bdd.dand b1 (Bdd.dnot b2) in
      BBool b
  | _ -> Console.error "internal error (lt)"

let rec eval (env: t Env.t) (e: exp) : t =
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
    | ULess, [e1; e2] -> lt (eval env e1) (eval env e2)
    | ULeq, [e1; e2] -> leq (eval env e1) (eval env e2)
    | USub, [e1; e2] -> Console.error "subtraction not implemented"
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
        match get_inner_type (oget v.vty) with
        | TOption ty -> ty
        | _ -> Console.error "internal error (eval_value)"
      in
      let dv = Generators.default_value ty in
      BOption (Bdd.dfalse mgr, eval_value env dv)
  | VOption (Some v) -> BOption (Bdd.dtrue mgr, eval_value env v)
  | VTuple vs -> BTuple (List.map (eval_value env) vs)
  | VMap _ | VClosure _ -> Console.error "internal error (eval_value)"
