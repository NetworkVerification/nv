open Nv_datastructures.AdjGraph
open Nv_lang.Syntax

(***
 * Functions to rewrite network declarations to include cases added by partitioning.
 ***)

(* Wrap the given init exp in a new exp of the form:
 * match x with
 * | out -> init u
 * | in -> init u
 * | _ -> init x
 * where the edge u~v has been partitioned into u~out and in~v.
*)
val transform_init : exp -> exp -> exp -> ty -> SrpRemapping.partitioned_srp -> exp

(* Wrap the given trans exp in a new exp of the form:
 * match e with
 * | u~out -> a
 * | in~v -> trans u~v a
 * | _ -> trans e a
 * where the edge u~v has been partitioned into u~out and in~v.
 * Note that the `trans u~v a` case is pulled from the previous exp.
*)
val transform_trans : exp -> ty -> SrpRemapping.partitioned_srp -> exp

(* NOTE: this function appears to be unnecessary in practice *)
(* Wrap the given merge exp in a new exp of the form:
 * match n with
 * | out -> y
 * | in -> x
 * | _ -> merge n x y
 * where the edge u~v has been partitioned into u~out and in~v.
*)
val transform_merge : exp -> ty -> SrpRemapping.partitioned_srp -> exp


val outputs_assert : exp -> exp -> ty -> SrpRemapping.partitioned_srp -> exp list

(* Wrap the given assert exp in a new exp that maps over new nodes.
 * TODO
*)
val transform_assert : exp -> SrpRemapping.partitioned_srp -> exp
