val flatten_ty : Syntax.ty -> Syntax.ty

(** [flatten ds] flattens nested tuples *)
val flatten : Syntax.declarations -> Syntax.declarations

val flatten_net : Syntax.network -> Syntax.network
    
