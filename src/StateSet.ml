open Cudd

type index_info = 
  | IBool of int 
  | IInt of int list
  | ITuple of index_info list 
  | IOption of int * index_info 
  [@@deriving eq, ord, show]

(* type state_set = 
  | SSBase of index_info * unit Bdd.t
  | SSMap of index_info * state_set Mtbdd.t *)

type state_set =
  | SSBool of unit Bdd.t
  | SSInt of unit Bdd.t list
  | SSTuple of state_set list
  | SSOption of unit Bdd.t * state_set
  | SSMap of state_set Mtbdd.t

let rec hash (s: state_set) : int =
  match s with
  | SSBool bdd -> Bdd.topvar bdd
  | SSInt bdds ->
      let f acc b = 31 * acc + (Bdd.topvar b) in
      List.fold_left f 0 bdds
  | SSTuple ss -> 
      let f acc s = 31 * acc + (hash s) in
      List.fold_left f 0 ss
  | SSOption (tag, s) -> 31 * Bdd.topvar tag + hash s
  | SSMap mbdd -> Mtbdd.topvar mbdd

  
let rec equal s1 s2 = 
  match s1, s2 with 
  | SSBool b1, SSBool b2 -> Bdd.is_equal b1 b2
  | SSInt bs1, SSInt bs2 -> equal_bdds bs1 bs2
  | SSTuple ss1, SSTuple ss2 -> equal_list ss1 ss2
  | SSOption (tag1, s1), SSOption (tag2, s2) -> Bdd.is_equal tag1 tag2 && equal s1 s2
  | SSMap m1, SSMap m2 -> Mtbdd.is_equal m1 m2
  | _, _ -> false

and equal_bdds ls1 ls2 = 
  match ls1, ls2 with 
  | [], [] -> true 
  | [], _ | _, [] -> false 
  | x::xtl, y::ytl -> Bdd.is_equal x y && equal_bdds xtl ytl

and equal_list ls1 ls2 = 
  match ls1, ls2 with 
  | [], [] -> true 
  | [], _ | _, [] -> false 
  | x::xtl, y::ytl -> equal x y && equal_list xtl ytl

let manager = Man.make_v ()

(* Bdd.ithvar manager ... *)
(* Mtbdd.cst manager tbl 3 *)

let tbl = Mtbdd.make_table ~hash:hash ~equal:equal

let foo (x: state_set Mtbdd.t) : state_set Mtbdd.t =
  Mapleaf.mapleaf1
    (fun a -> Cudd.Mtbdd.unique tbl (Cudd.Mtbdd.get a))
    x
