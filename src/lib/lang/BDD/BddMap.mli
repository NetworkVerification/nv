open Cudd
open Syntax
open Nv_datastructures

type t = mtbdd

val create : key_ty:ty -> value -> t

val default_value : ty -> value

val value_to_bdd: value -> Bdd.vt

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

val bindings_repr : t -> (value * value) list

val bindings_all : t -> (value * value) list

val from_bindings : key_ty:ty -> (value * value) list * value -> t

val equal : t -> t -> bool

(** * Printing BDD values*)

(** Type of multivalues*)
type multiValue =
  | MUnit
  | MBool of bool option (* Booleans are either true, false, or "Top" *)
  | MInt of ((Integer.t * Integer.t) list) (* Integers are represented as ranges *)
  | MBit of (bool option) array
  | MOption of (bool option * multiValue)
  | MTuple of multiValue list (* Tuple of elements *)
  | MNode of (bool option) array
  | MEdge of (bool option) array * (bool option) array

val bindingsExact : t -> (multiValue * value) list

val multiValue_to_string : multiValue -> string
