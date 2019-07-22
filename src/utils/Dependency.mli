open Batteries
open Syntax
open Collections

(* Very simple dependency analysis for heavily-simplified NV programs. It
   assumes the following have been done: Inlining, Record Unrolling, Map Unrolling,
   Option Unboxing, Tuple Flattening, Renaming. In particular, we should encounter
   no records, maps, or options *)

type dependency =
  | ArgDep of int (* Argument number *)
  | VarDep of var (* Variable name *)
;;

module DepSet : BatSet.S with type elt = dependency

type depresult =
  | DBase of DepSet.t
  | DTuple of depresult list
;;

type depmap = depresult VarMap.t
;;

val dependency_to_string : dependency -> string
val depresult_to_string : depresult -> string

(* Expects to be given a function definition, presumably that of trans/merge/init.
   But it should work for any built-in functions. *)
val compute_dependencies_func : exp -> depresult
