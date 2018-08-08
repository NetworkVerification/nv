open BatMap

type ('k, 'v) t

val create : ('k -> 'k -> int) -> 'v -> ('k, 'v) t

val bindings : ('k, 'v) t -> ('k * 'v) list * 'v

val from_bindings : ('k -> 'k -> int) -> ('k * 'v) list * 'v -> ('k, 'v) t

val find : ('k, 'v) t -> 'k -> 'v

val update : ('k, 'v) t -> 'k -> 'v -> ('k, 'v) t

val map : ('v -> 'w) -> ('k, 'v) t -> ('k, 'w) t

val merge : ('u -> 'v -> 'w) -> ('k, 'u) t -> ('k, 'v) t -> ('k, 'w) t

val equal : ('v -> 'v -> bool) -> ('k, 'v) t -> ('k, 'v) t -> bool

val compare : ('v -> 'v -> int) -> ('k, 'v) t -> ('k, 'v) t -> int
