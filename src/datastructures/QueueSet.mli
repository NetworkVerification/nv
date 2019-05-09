(* Purely functional queue that does not permit duplicates *)

type 'a queue

val empty : ('a -> 'a -> int) -> 'a queue

val add : 'a queue -> 'a -> 'a queue

val add_all : 'a queue -> 'a list -> 'a queue

val pop : 'a queue -> ('a * 'a queue) option

val iter : ('a -> unit) -> 'a queue -> unit
