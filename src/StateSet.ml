open Cudd

type bdd_indexes = 
  | IBool of int 
  | IInt of int list
  | ITuple of bdd_indexes list 
  | IOption of int * bdd_indexes 
  | IMap of bdd_indexes
  [@@deriving eq, ord, show]

type sset = 
  | SSBase of bdd_indexes * unit Bdd.t
  | SSMap of bdd_indexes * sset Mtbdd.t

let rec hash (s: sset) : int =
  match s with
  | SSBase (ii, bdd) -> Bdd.topvar bdd
  | SSMap (ii, mbdd) -> Mtbdd.topvar mbdd

  
let rec equal_sset s1 s2 = 
  match s1, s2 with 
  | SSBase (i1,b1), SSBase (i2,b2) -> Bdd.is_equal b1 b2 && equal_bdd_indexes i1 i2
  | SSMap (i1,m1), SSMap (i2,m2) -> Mtbdd.is_equal m1 m2 && equal_bdd_indexes i1 i2
  | _, _ -> false

let manager = Man.make_v ()

(* Bdd.ithvar manager ... *)
(* Mtbdd.cst manager tbl 3 *)

let tbl = Mtbdd.make_table ~hash:hash ~equal:equal_sset

let foo (x: sset Mtbdd.t) : sset Mtbdd.t =
  Mapleaf.mapleaf1
    (fun a -> Cudd.Mtbdd.unique tbl (Cudd.Mtbdd.get a))
    x
