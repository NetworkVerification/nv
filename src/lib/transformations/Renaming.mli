open Nv_lang
open Nv_solution
open Nv_kirigami

val alpha_convert_exp
  :  Nv_datastructures.Var.t Nv_datastructures.Env.t
  -> Syntax.exp
  -> Syntax.exp

val alpha_convert_partitioned_declarations
  :  Partition.partitioned_decls
  -> Partition.partitioned_decls * (Solution.t -> Solution.t)

val alpha_convert_declarations
  :  Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)
