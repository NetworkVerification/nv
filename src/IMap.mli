open Unsigned

type 'a t

val create : UInt32.t -> 'a t
val length : 'a t -> UInt32.t
val bindings : 'a t -> (UInt32.t * 'a) list
val get : 'a t -> UInt32.t -> 'a option
val set : 'a t -> UInt32.t -> 'a -> 'a t
val map : ('a -> 'b) -> 'a t -> 'b t
val merge : ('a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t
val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
