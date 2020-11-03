open Syntax

val show_exp : exp -> string
val show_exp : show_meta:bool -> exp -> string
val show_value : show_meta:bool -> value -> string
val show_ty : ?show_links:bool -> ty -> string
