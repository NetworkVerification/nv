open Cudd
open Syntax

type t = mtbdd

val create : key_ty:ty -> value -> t

val default_value : ty -> value

val map :
  op_key:exp * value BatSet.PSet.t -> (value -> value) -> t -> t

val map_when :
  op_key:exp * value BatSet.PSet.t
  -> bool Mtbdd.t
  -> (value -> value)
  -> t
  -> t

val map_ite :
  op_key1:exp * value BatSet.PSet.t
  -> op_key2:exp * value BatSet.PSet.t
  -> bool Mtbdd.t
  -> (value -> value)
  -> (value -> value)
  -> t
  -> t

val merge :
  ?opt:value * value * value * value
  -> op_key:exp * value BatSet.PSet.t
  -> (value -> value -> value)
  -> t
  -> t
  -> t

val find : t -> value -> value

val update : t -> value -> value -> t

val bindings : t -> (value * value) list * value

val from_bindings : key_ty:ty -> (value * value) list * value -> t

val equal : t -> t -> bool
