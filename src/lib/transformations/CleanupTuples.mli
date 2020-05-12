(* Replaces all 0-element tuples in the program with unit,
   and all 1-element tuples with their only element. *)
open Nv_lang.Syntax
open Nv_solution

val cleanup_declarations : declarations -> declarations * Solution.map_back