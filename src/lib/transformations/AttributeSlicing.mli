open Nv_lang.Syntax
open Nv_solution
open Nv_utils.OCamlUtils

val slice_network : network -> (network * (Solution.t -> Solution.t)) delayed list
