type t = {start: int; finish: int} [@@deriving show, ord]

val extend : t -> t -> t

val default : t
