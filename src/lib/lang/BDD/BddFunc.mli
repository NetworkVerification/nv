open Cudd
open Syntax

type t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BOption of Bdd.vt * t
  | Tuple of t list
  | BMap of BddMap.t
  | Value of Syntax.value

val bdd_of_bool: bool -> Cudd.Man.v Cudd.Bdd.t

val create_value : ty -> t

val eval : t Nv_datastructures.Env.t -> exp -> t

val eval_value :value -> t

val wrap_mtbdd : Bdd.vt -> bool Mtbdd.t
