type t = {start: int; finish: int} [@@deriving show]

val extend : t -> t -> t

val default : t
