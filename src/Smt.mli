open Collections
open Syntax

type smt_env =
  { solver: Z3.Solver.solver
  ; ctx: Z3.context
  ; symbolics: (Var.t * ty_or_exp) list }

type smt_result = Unsat | Unknown | Sat of Solution.t

val exp_to_z3 : smt_env -> string -> exp -> Z3.Expr.expr

val z3_to_value : Z3.Model.model -> Z3.Expr.expr -> value

val symvar_assign : declarations -> value StringMap.t option

val solve :
  ?symbolic_vars:(Var.t * exp) list -> declarations -> smt_result
