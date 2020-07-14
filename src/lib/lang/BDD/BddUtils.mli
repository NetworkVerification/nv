open Nv_datastructures 
open Cudd
(** BDD/MTBDD manager *)
val mgr: Cudd.Man.v Cudd.Man.t

val tbl: 'a Cudd.Mtbdd.table
(** This is a bit of a hack, but to avoid a bunch of modules, we assume that the interpreter is always using tbl_nv. 
    The native simulator is using tbl, except for BddFunc which uses tbl_nv *)
val tbl_nv: Syntax.value Cudd.Mtbdd.table
val tbl_bool: bool Cudd.Mtbdd.table

(* Given a type returns the number of decision variables required to represent its values *)
val ty_to_size: Syntax.ty -> int

(** Sets number of variables in the manager *)
val set_size : int -> unit

(** [ithvar i] returns decision variable i from the manager *)
val ithvar: int -> Cudd.Man.v Cudd.Bdd.t

(** Given an integer n and an int i returns the ith-bit of n. *)
val get_bit : Integer.t -> int -> bool

(** [mk_int i idx] *)
val mk_int: Integer.t -> int -> Cudd.Man.v Cudd.Bdd.t

val tbool_to_bool: Cudd.Man.tbool -> bool

val tbool_to_obool: Cudd.Man.tbool -> bool option

val count_tops: Cudd.Man.tbool array -> int -> int

val expand: Cudd.Man.tbool list -> int -> Cudd.Man.tbool list list