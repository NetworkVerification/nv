open Cudd
open Syntax

type key_index =
  | IBool of int
  | IInt of int list
  | ITuple of key_index list
  | IOption of int * key_index
  | IMap of key_index
[@@deriving eq, ord, show]

type sset = SSBase of value | SSMap of key_index * sset Mtbdd.t

let rec hash_bdd_index bi =
  match bi with
  | IBool i -> i
  | IInt is -> List.fold_left (fun acc i -> (31 * acc) + i) 0 is
  | ITuple is ->
      List.fold_left (fun acc i -> (31 * acc) + hash_bdd_index i) 0 is
  | IOption (tag, i) -> (31 * tag) + hash_bdd_index i
  | IMap i -> 5 + hash_bdd_index i

let rec hash_sset (s: sset) : int =
  match s with
  | SSBase v -> Hashtbl.hash v
  | SSMap (ii, mbdd) -> Mtbdd.topvar mbdd

let rec equal_sset s1 s2 =
  match (s1, s2) with
  | SSBase v1, SSBase v2 -> compare_values v1 v2 = 0
  | SSMap (i1, m1), SSMap (i2, m2) ->
      Mtbdd.is_equal m1 m2 && equal_key_index i1 i2
  | _, _ -> false

let manager = Man.make_v ()

(* Bdd.ithvar manager ... *)
(* Mtbdd.cst manager tbl 3 *)

let tbl = Mtbdd.make_table ~hash:hash_sset ~equal:equal_sset

let foo (x: sset Mtbdd.t) : sset Mtbdd.t =
  Mapleaf.mapleaf1 (fun a -> Cudd.Mtbdd.unique tbl (Cudd.Mtbdd.get a)) x
