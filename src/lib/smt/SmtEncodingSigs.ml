open Nv_lang
open SmtUtils
open SmtLang

module type ExprEncoding =
sig
  type 'a t

  (** Translates a [Syntax.ty] to an SMT sort *)
  val ty_to_sorts : Syntax.ty -> sort t
  val encode_exp_z3 : string -> smt_env -> Syntax.exp -> term t
  val create_strings : string -> Syntax.ty -> string t
  val create_vars : smt_env -> string -> Syntax.var -> string
  val mk_constant : smt_env -> ?cdescr:string -> ?cloc:Nv_datastructures.Span.t
    -> string -> sort -> term
  val lift1: ('a -> 'b) -> 'a t -> 'b t
  val lift2: ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val to_list : 'a t -> 'a list
  val of_list : 'a list -> 'a t
  val combine_term: term t -> term
  val add_symbolic: smt_env -> Nv_datastructures.Var.t t -> Syntax.ty_or_exp -> unit
  val init_solver: (Nv_datastructures.Var.t * Syntax.ty_or_exp) list ->
    labels:(Syntax.var * Syntax.ty) list -> smt_env
end

module type Encoding =
  sig
    type network_type
    val encode_z3: network_type -> smt_env
    val add_symbolic_constraints: smt_env ->  Syntax.exp list -> Syntax.ty_or_exp Collections.VarMap.t -> unit
end
