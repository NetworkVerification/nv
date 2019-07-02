open Cudd
open Syntax

type t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BTuple of t list
  | BOption of Bdd.vt * t

val create_value : ty -> t

val eval : t Env.t -> exp -> t

val eval_value : t Env.t -> value -> t

val wrap_mtbdd : Bdd.vt -> bool Mtbdd.t
