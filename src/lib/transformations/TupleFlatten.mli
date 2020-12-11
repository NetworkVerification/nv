open Nv_lang.Syntax
open Nv_solution

val proj_symbolic : var * ty_or_exp -> (var * ty_or_exp) list

(** [flatten ds] flattens nested tuples *)
val flatten_declarations : declarations -> declarations * Solution.map_back

(* (\** [unflatten_val v ty] will unflatten the value [v] according to the type [ty] *\)
 * val unflatten_val : value -> ty -> value *)

(* (\** [unflatten_sol ty sol] will unflatten the labels in solution [sol]
 *    according to the type attribute type [ty] *\)
 * val unflatten_sol : ty -> Solution.t -> Solution.t *)
