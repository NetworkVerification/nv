open Nv_lang.Syntax
open Nv_solution

val slice_network : network -> (network * (Solution.t -> Solution.t)) list
