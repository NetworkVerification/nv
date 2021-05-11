open Syntax

val map_exp : (exp -> exp) -> exp -> exp
val map_exp_decl : (declaration -> exp -> exp) -> declaration -> declaration
val map_exp_decls : (declaration -> exp -> exp) -> declarations -> declarations
val iter_exp : (exp -> unit) -> exp -> unit
val iter_exp_decl : (declaration -> exp -> unit) -> declaration -> unit
val iter_exp_decls : (declaration -> exp -> unit) -> declarations -> unit
