val flatten_ty : Syntax.ty -> Syntax.ty

(** [flatten ds] flattens nested tuples *)
val flatten : Syntax.declarations -> Syntax.declarations
