type t = {fname: string; start: int; finish: int} [@@deriving show, ord]

val extend : t -> t -> t

val default : t

val show_span : t -> string
