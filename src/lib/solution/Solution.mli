open Nv_datastructures.AdjGraph
open Nv_lang.Collections
open Nv_lang.Syntax

type t =
  { symbolics: value VarMap.t
  ; labels: value VertexMap.t
  ; assertions: bool VertexMap.t option
  ; mask: value option  }

type map_back = t -> t

val print_masked_type : ty -> t -> string

val print_solution : t -> unit

val mask_type_ty : ty -> ty
(* val mask_type_sol : t -> ty *)
(* Given a value, creates a mask where every part of the value is displayed *)
val value_to_mask : value -> value
