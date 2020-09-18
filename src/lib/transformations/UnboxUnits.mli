(* Replace all units in the program with booleans (false) so that we don't
   have to worry about them in SMT *)
open Nv_lang.Syntax
open Nv_solution

val unbox_declarations : declarations -> declarations * Solution.map_back
