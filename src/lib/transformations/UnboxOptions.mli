open Nv_lang.Syntax
open Nv_solution

(* Convert all option values to tuples of (bool, v), where
   None is represented by (false, default_value)
   Some v is represented by (true, v)
*)

val unbox_declarations : declarations -> declarations * Solution.map_back