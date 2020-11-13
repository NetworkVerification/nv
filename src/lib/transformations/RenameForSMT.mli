open Nv_lang
open Nv_solution
open Nv_kirigami

val rename_declarations
  :  Syntax.declarations
  -> Syntax.declarations * (Solution.t -> Solution.t)

val rename_partitioned_declarations
  :  Partition.partitioned_decls
  -> Partition.partitioned_decls * (Solution.t -> Solution.t)
