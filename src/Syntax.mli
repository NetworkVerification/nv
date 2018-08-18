open Cudd
open Unsigned

type index = UInt32.t

type level = int

type tyname = Var.t

type ty =
  | TVar of tyvar ref
  | QVar of tyname
  | TBool
  | TInt of index
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty

and tyvar = Unbound of tyname * level | Link of ty

type var = Var.t

type op =
  | And
  | Or
  | Not
  | UAdd
  | USub
  | UEq
  | ULess
  | ULeq
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMapFilter
  | MMerge

type pattern =
  | PWild
  | PVar of var
  | PBool of bool
  | PUInt32 of UInt32.t
  | PTuple of pattern list
  | POption of pattern option

type v =
  | VBool of bool
  | VUInt32 of UInt32.t
  | VMap of mtbdd
  | VTuple of value list
  | VOption of value option
  | VClosure of closure

and mtbdd = value Mtbdd.t * ty

and value = {v: v; vty: ty option; vspan: Span.t}

and e =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | ESome of exp
  | EMatch of exp * branches
  | ETy of exp * ty

and exp = {e: e; ety: ty option; espan: Span.t}

and branches = (pattern * exp) list

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and closure = env * func

and env = {ty: ty Env.t; value: value Env.t}

and ty_or_exp = Ty of ty | Exp of exp

type declaration =
  | DLet of var * ty option * exp
  | DSymbolic of var * ty_or_exp
  | DATy of ty
  | DMerge of exp
  | DTrans of exp
  | DInit of exp
  | DAssert of exp
  | DRequire of exp
  | DNodes of UInt32.t
  | DEdges of (UInt32.t * UInt32.t) list

type declarations = declaration list

(* Utilities *)

val arity : op -> int

val tint : ty

val exp : e -> exp

val wrap : exp -> e -> exp

val value : v -> value

val e_val : v -> exp

val func : var -> exp -> func

val lam : var -> exp -> exp

val annot : ty -> exp -> exp

val annotv : ty -> value -> value

val is_value : exp -> bool

val to_value : exp -> value

val oget : 'a option -> 'a

val lams : var list -> exp -> exp

val apps : exp -> exp list -> exp

val apply_closure : closure -> value list -> exp

val get_attr_type : declarations -> ty option

val get_merge : declarations -> exp option

val get_trans : declarations -> exp option

val get_init : declarations -> exp option

val get_assert : declarations -> exp option

val get_edges : declarations -> (UInt32.t * UInt32.t) list option

val get_nodes : declarations -> UInt32.t option

val get_symbolics : declarations -> (var * ty_or_exp) list

val get_requires : declarations -> exp list

val equal_values : value -> value -> bool

val hash_value : value -> int

val get_inner_type : ty -> ty

module BddMap : sig
  type t = mtbdd

  val create : key_ty:ty -> value -> t

  val map : (value -> value) -> t -> t

  val map_when : Bdd.vt -> (value -> value) -> t -> t

  val merge : (value -> value -> value) -> t -> t -> t

  val find : t -> value -> value

  val update : t -> value -> value -> t

  val bindings : t -> (value * value) list * value

  val from_bindings : key_ty:ty -> (value * value) list * value -> t

  val equal : t -> t -> bool
end

module BddFunc : sig
  type t =
    | BBool of Bdd.vt
    | BInt of Bdd.vt array
    | BTuple of t list
    | BOption of Bdd.vt * t

  val create_value : ty -> t

  val eval : t Env.t -> exp -> t

  val eval_value : t Env.t -> value -> t
end

val default_value : ty -> value
