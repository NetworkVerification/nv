open BatMap

type ('k, 'v) t

val create : ('k -> 'k -> int) -> 'v -> ('k, 'v) t

val bindings : ('k, 'v) t -> ('k * 'v) list * 'v

val from_bindings :
  ('k -> 'k -> int) -> ('k * 'v) list * 'v -> ('k, 'v) t

val find : ('k, 'v) t -> 'k -> 'v

val update : ('k, 'v) t -> 'k -> 'v -> ('k, 'v) t

val map : ('v -> 'v) -> ('k, 'v) t -> ('k, 'v) t

val merge :
  ('v -> 'v -> 'v) -> ('k, 'v) t -> ('k, 'v) t -> ('k, 'v) t

val equal : ('v -> 'v -> bool) -> ('k, 'v) t -> ('k, 'v) t -> bool

val compare : ('v -> 'v -> int) -> ('k, 'v) t -> ('k, 'v) t -> int
