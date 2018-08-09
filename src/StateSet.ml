open Cudd

type bdd_index =
  | IBool of int
  | IInt of int list
  | ITuple of bdd_index list
  | IOption of int * bdd_index
  | IMap of bdd_index
[@@deriving eq, ord, show]

type sset =
  | SSBase of bdd_index * unit Bdd.t
  | SSMap of bdd_index * sset Mtbdd.t

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
  | SSBase (ii, bdd) -> Bdd.topvar bdd
  | SSMap (ii, mbdd) -> Mtbdd.topvar mbdd

let rec equal_sset s1 s2 =
  match (s1, s2) with
  | SSBase (i1, b1), SSBase (i2, b2) ->
      Bdd.is_equal b1 b2 && equal_bdd_index i1 i2
  | SSMap (i1, m1), SSMap (i2, m2) ->
      Mtbdd.is_equal m1 m2 && equal_bdd_index i1 i2
  | _, _ -> false

let manager = Man.make_v ()

(* Bdd.ithvar manager ... *)
(* Mtbdd.cst manager tbl 3 *)

let tbl = Mtbdd.make_table ~hash:hash_sset ~equal:equal_sset

let foo (x: sset Mtbdd.t) : sset Mtbdd.t =
  Mapleaf.mapleaf1 (fun a -> Cudd.Mtbdd.unique tbl (Cudd.Mtbdd.get a)) x
