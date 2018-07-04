open Unsigned

type 'a t

exception Out_of_bounds of UInt32.t

val create : UInt32.t -> 'a -> 'a t

val length : 'a t -> UInt32.t

val bindings : 'a t -> (UInt32.t * 'a) list * 'a

val from_bindings : UInt32.t -> (UInt32.t * 'a) list * 'a -> 'a t

val find : 'a t -> UInt32.t -> 'a

val update : 'a t -> UInt32.t -> 'a -> 'a t

val map : ('a -> 'b) -> 'a t -> 'b t

val merge : ('a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
