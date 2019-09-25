open Nv_datastructures
open Nv_lang

(***
 * Functions to rewrite Syntax.network declarations to include cases added by partitioning.
 ***)

(* Wrap the given init exp in a new exp of the form:
 * match x with
 * | out -> init u
 * | in -> init u
 * | _ -> init x
 * where the edge u~v has been partitioned into u~out and in~v.
 *)
val transform_init : (Syntax.exp) -> (OpenAdjGraph.t) -> ?intf:Syntax.value option AdjGraph.EdgeMap.t -> (Syntax.exp)

(* Wrap the given trans exp in a new exp of the form:
 * match e with
 * | u~out -> a
 * | in~v -> trans u~v a
 * | _ -> trans e a
 * where the edge u~v has been partitioned into u~out and in~v.
 * Note that the `trans u~v a` case is pulled from the previous exp.
 *)
val transform_trans : (Syntax.exp) -> (OpenAdjGraph.t) -> (Syntax.exp)

(* Wrap the given merge exp in a new exp of the form:
 * match n with
 * | out -> y
 * | in -> x
 * | _ -> merge n x y
 * where the edge u~v has been partitioned into u~out and in~v.
 *)
val transform_merge : (Syntax.exp) -> (OpenAdjGraph.t) -> (Syntax.exp)
