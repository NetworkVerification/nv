(* Pervasives *)
open Syntax

let var x = Var.create x

(* FIXME: (x, e) doesn't match {arg: var; argty: ty option; resty: ty option; body: exp} *)
(* let lam x e = EFun (x, e) *)

(* let exp x = Syntax.EVar x *)

let mapf =
  let f = var "f" in
  let m = var "m" in
  lam f (lam m (eop MMap [evar f; evar m]))

let joinf =
  let m = var "m" in
  let n = var "n" in
  lam m (lam n (eop MMerge [evar m; evar n]))
  (* lam m (lam n (Syntax.EOp (MMerge, [exp m; exp n]))) *)

let vecf =
  let d = var "d" in
  let n = var "n" in
  lam n (lam d (eop MCreate [evar d]))
  (* lam n (lam d (Syntax.EOp (MCreate, [exp d]))) *)

let pervasives = [("map", mapf); ("join", joinf); ("vec", vecf)]
