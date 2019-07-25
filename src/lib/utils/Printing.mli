(* Printing utilities *)

val list_to_string : ('a -> string) -> 'a list -> string

val op_to_string : Nv_core.Syntax.op -> string

val tyvar_to_string : Nv_core.Syntax.tyvar -> string

val ty_to_string : Nv_core.Syntax.ty -> string

val value_to_string : Nv_core.Syntax.value -> string

val pattern_to_string : Nv_core.Syntax.pattern -> string

val exp_to_string : Nv_core.Syntax.exp -> string

val func_to_string : Nv_core.Syntax.func -> string

val closure_to_string : Nv_core.Syntax.closure -> string

val env_to_string : Nv_core.Syntax.env -> string

val declaration_to_string : Nv_core.Syntax.declaration -> string

val declarations_to_string : Nv_core.Syntax.declarations -> string

val network_to_string : ?show_topology:bool -> Nv_core.Syntax.network -> string
