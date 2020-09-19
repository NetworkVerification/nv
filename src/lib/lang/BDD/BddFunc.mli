open Cudd
open Syntax

type t =
  | BBool of Bdd.vt
  | BInt of Bdd.vt array
  | BOption of Bdd.vt * t
  | Tuple of t list
  | BMap of BddMap.t
  | Value of Syntax.value

val bdd_of_bool : bool -> Cudd.Man.v Cudd.Bdd.t

val value_mtbdd_bool_mtbdd
  :  value Cudd.Mtbdd.unique Cudd.Vdd.t
  -> bool Cudd.Mtbdd.unique Cudd.Vdd.t

(** Given a type, creates a BDD value representing all possible values of this type. *)
val create_value : ty -> t

(** Given an environment and an expression, creates a BDD expression that captures its semantics. *)
val eval : t Nv_datastructures.Env.t -> exp -> t

(** Evaluates a value to a BDD *)
val eval_value : value -> t

val wrap_mtbdd : Bdd.vt -> bool Mtbdd.t
