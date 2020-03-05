(* Printing utilities *)

val list_to_string : ('a -> string) -> 'a list -> string

val op_to_string : Syntax.op -> string

val tyvar_to_string : Syntax.tyvar -> string

val ty_to_string : Syntax.ty -> string

val value_to_string : ?show_types:bool -> Syntax.value -> string

val pattern_to_string : Syntax.pattern -> string

val exp_to_string : ?show_types:bool -> Syntax.exp -> string

val func_to_string : ?show_types:bool -> Syntax.func -> string

val closure_to_string : ?show_types:bool -> Syntax.closure -> string

val env_to_string : ?show_types:bool -> Syntax.env -> string

val declaration_to_string : ?show_types:bool -> Syntax.declaration -> string

val declarations_to_string : ?show_types:bool -> Syntax.declarations -> string

val network_to_string : ?show_types:bool -> ?show_topology:bool -> Syntax.network -> string
