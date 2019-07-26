open Nv_lang
open Nv_solution

val unbox_ty : Syntax.ty -> Syntax.ty

(** [unbox ds] converts options in an NV program to a tuple of the form (bool,val)
   where false represents None and true Some *)
val unbox : Syntax.declarations -> Syntax.declarations

val unbox_net : Syntax.network -> Syntax.network * (Solution.t -> Solution.t)

val unbox_srp : Syntax.srp_unfold -> Syntax.srp_unfold * (Solution.t -> Solution.t)
