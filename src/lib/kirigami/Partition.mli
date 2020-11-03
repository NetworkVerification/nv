(* Partitioning utilities and partition interface definitions *)
open Batteries
open Nv_datastructures
open Nv_lang
open Nv_lang.Syntax
open Nv_solution.Solution

(* Describe how the transfer function should be decomposed.
 * Some types of networks require different settings of this,
 * depending on how they transfer routes.
 * Future work will involve providing the transcomp as part of
 * a solution (when an interface is provided) to describe how
 * to decompose the transfer function.
 *  Figuring that out is future work. *)
type transcomp =
  (* Decompose the original transfer e into two parts e1 and e2,
   * where e1 is performed on the base~output edge and e2 is
   * performed on the input~base edge. *)
  | Decomposed of exp * exp
  (* Shorthand for (Decomposed e identity). *)
  | OutputTrans
  (* Shorthand for (Decomposed identity e). *)
  | InputTrans

(** Separation of the purposes of the declarations
 ** for a given partitioned SRP. *)
type partitioned_decls =
  { (* new DSymbolic decls *)
    (* symbolics: declaration list; *)
    (* new DRequire decls and their corresponding partition ranks *)
    lesser_hyps : declaration list
  ; greater_hyps : declaration list
  ; (* new DAssert decls for checking hypotheses *)
    guarantees : declaration list
  ; (* old DAssert decls for testing network properties *)
    properties : declaration list
  ; (* all other network decls, including those defining essential behaviour (solution, topology) *)
    network : declaration list
  }

(* Sum type that distinguishes partitioned versus unpartitioned networks,
 * for the purpose of lifting operations over declarations. *)
type declaration_group =
  | Unpartitioned of declarations
  | Partitioned of partitioned_decls

(** Create a list of Syntax.declarations,
 * where a new set of declarations for a given network is produced
 * for each possible partition in the given declarations.
 * Also return a set identifying which asserts and requires are added as part of kirigami,
 ** and which are part of the base declarations.
*)
val divide_decls : Cmdline.t -> declarations -> declaration_group list

val lift : (declarations -> declarations) -> declaration_group -> declaration_group

val lift_mb
  :  (declarations -> declarations * map_back)
  -> declaration_group
  -> declaration_group * map_back
