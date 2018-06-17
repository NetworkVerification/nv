(* Program Variables *)

type t
val fresh : string -> t
val name : t -> string
val to_var : string * int -> t
val from_var : t -> string * int
val to_string : t -> string
val equals : t -> t -> bool
val compare : t -> t -> int
