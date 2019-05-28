val flatten_ty : Syntax.ty -> Syntax.ty

(** [flatten ds] flattens nested tuples *)
val flatten : Syntax.declarations -> Syntax.declarations

val flatten_net : Syntax.network -> Syntax.network * (Solution.t -> Solution.t)

(* (\** [unflatten_val v ty] will unflatten the value [v] according to the type [ty] *\) 
 * val unflatten_val : Syntax.value -> Syntax.ty -> Syntax.value *)

(* (\** [unflatten_sol ty sol] will unflatten the labels in solution [sol]
 *    according to the type attribute type [ty] *\)   
 * val unflatten_sol : Syntax.ty -> Solution.t -> Solution.t *)
