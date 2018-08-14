open Syntax

type t

val map: (value -> value) -> t -> t 

val map_when: (value -> bool) -> (value -> value) -> t -> t

val merge: (value -> value -> value) -> t -> t -> t

val get: value -> t -> value

val set: value -> value -> t -> t

val compare_maps: t -> t -> int

val equal_maps: t -> t -> bool

val hash_map: t -> int
