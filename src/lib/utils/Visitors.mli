open Nv_core.Syntax

val iter_exp : (exp -> unit) -> exp -> unit

val iter_exp_decl :
  (declaration -> exp -> unit) -> declaration -> unit

val iter_exp_decls :
  (declaration -> exp -> unit) -> declarations -> unit

val iter_exp_net : (exp -> unit) -> network -> unit
