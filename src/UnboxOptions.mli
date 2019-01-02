val unbox_ty : Syntax.ty -> Syntax.ty

(** [unbox ds] converts options in an NV program to a tuple of the form (bool,val)
   where false represents None and true Some *)
val unbox : Syntax.declarations -> Syntax.declarations
