open Syntax

type t

val init : int -> unit

val create : key_ty:ty -> value -> t

val bindings : t -> (value * value) list

val from_bindings : (value * value) list * value -> t

val map : (value -> value) -> t -> t

val map_when : (value -> bool) -> (value -> value) -> t -> t

val merge : (value -> value -> value) -> t -> t -> t

val find : t -> value -> value

val update : t -> value -> value -> t

val compare_maps : t -> t -> int

val equal_maps : t -> t -> bool

val hash_map : t -> int

val show_map : t -> string
