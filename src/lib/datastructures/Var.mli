(* Program Variables *)

type t [@@deriving show]

val create : string -> t

val fresh : string -> t

val reset : unit -> unit

val name : t -> string

val to_var : string * int -> t

val from_var : t -> string * int

val to_string : t -> string

val to_string_delim : string -> t -> string

(* Inverse of to_string. Do not use for other values. *)
val of_var_string : string -> t

val equal : t -> t -> bool

(* Alias for equal TODO: Refactor this out*)
val equals : t -> t -> bool

val equal_names : t -> t -> bool

val compare : t -> t -> int
