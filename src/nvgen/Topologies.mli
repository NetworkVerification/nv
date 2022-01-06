open Nv_datastructures
open Nv_lang

type topology = private
  | Fattree of int
  | FullMesh of int
  | Ring of int
  | Star of int
  | Rand of int * float
[@@deriving show]

type fatLevel =
  | Core
  | Aggregation
  | Edge

val star : int -> topology

val ring : int -> topology

val full_mesh : int -> topology

val rand : int -> float -> topology

val parse_string : string -> topology option

(** Construct an AdjGraph from a topology. *)
val construct : topology -> AdjGraph.t

(** Return the nodes and edges declarations for the given AdjGraph. *)
val to_decls : AdjGraph.t -> Syntax.declarations
