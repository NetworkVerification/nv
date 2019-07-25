(* Pervasives *)

open Syntax

let var x = Var.create x

let lam x e = EFun (x, e)

let exp x = EVar x

let mapf =
  let f = var "f" in
  let m = var "m" in
  lam f (lam m (EOp (MMap, [exp f; exp m])))

let joinf =
  let m = var "m" in
  let n = var "n" in
  lam m (lam n (EOp (MMerge, [exp m; exp n])))

let vecf =
  let d = var "d" in
  lam n (lam d (EOp (MCreate, [exp d])))

let pervasives = [("map", mapf); ("join", joinf); ("vec", vecf)]
