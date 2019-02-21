open Cudd

type index = int

type bitwidth = int

type level = int

type tyname = Var.t

type ty =
  | TVar of tyvar ref
  | QVar of tyname
  | TBool
  | TInt of bitwidth
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
  | UAdd of bitwidth
  | USub of bitwidth
  | UEq
  | ULess of bitwidth
  | ULeq of bitwidth
  | AtMost of int
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
  | PInt of Integer.t
  | PTuple of pattern list
  | POption of pattern option

module Pat : Map.OrderedType with type t = pattern

module PatMap : BatMap.S with type key = Pat.t

module Branch :
  sig
  
    type 'a t

    val compare: 'a t -> 'a t -> int
    val addBranch: Pat.t -> 'a -> 'a t -> 'a t
    val mapBranches: (Pat.t * 'a -> Pat.t * 'a) -> 'a t -> 'a t
    val iterBranches: (Pat.t * 'a -> unit) -> 'a t -> unit
    val lookUpPat: Pat.t -> 'a t -> 'a
    val popBranch: 'a t -> ((Pat.t * 'a) * 'a t) option
    val empty : 'a t
    val isEmpty: 'a t -> bool
    val optimize: 'a t -> 'a t
  end

type v = private
  | VBool of bool
  | VInt of Integer.t
  | VMap of mtbdd
  | VTuple of value list
  | VOption of value option
  | VClosure of closure

and mtbdd = value Mtbdd.t * ty

and value = private
  {v: v; vty: ty option; vspan: Span.t; vtag: int; vhkey: int}

and e = private
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

and exp = private
  {e: e; ety: ty option; espan: Span.t; etag: int; ehkey: int}

and branches = exp Branch.t

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
  | DNodes of Integer.t
  | DEdges of (Integer.t * Integer.t) list

type declarations = declaration list

type network =
  { attr_type    : ty;
    init         : exp;
    trans        : exp;
    merge        : exp;
    assertion    : exp option;
    symbolics    : (var * ty_or_exp) list;
    defs         : (var * ty option * exp) list; 
    requires     : exp list;
    graph        : AdjGraph.t;
  }

  
(* Constructors *)

val vbool : bool -> value

val vint : Integer.t -> value

val vmap : mtbdd -> value

val vtuple : value list -> value

val voption : value option -> value

val vclosure : closure -> value

val evar : var -> exp

val e_val : value -> exp

val eop : op -> exp list -> exp

val efun : func -> exp

val eapp : exp -> exp -> exp

val eif : exp -> exp -> exp -> exp

val elet : Var.t -> exp -> exp -> exp

val etuple : exp list -> exp

val esome : exp -> exp

val ematch : exp -> branches -> exp

val ety : exp -> ty -> exp

val deconstructFun: exp -> func

(* Utilities *)

val arity : op -> int

val tint_of_size : int -> ty

val tint_of_value : Integer.t -> ty

val exp : e -> exp

val value : v -> value

val aexp : exp * ty option * Span.t -> exp

val avalue : value * ty option * Span.t -> value

val annot : ty -> exp -> exp

val annotv : ty -> value -> value

val wrap : exp -> exp -> exp

val exp_of_v : v -> exp

val exp_of_value : value -> exp

val func : var -> exp -> func

val funcFull : var -> ty option -> ty option -> exp -> func

val efunc : func -> exp

val lam : var -> exp -> exp

val is_value : exp -> bool

val to_value : exp -> value

val oget : 'a option -> 'a

val omap : ('a -> 'b) -> 'a option -> 'b option

val lams : var list -> exp -> exp

val apps : exp -> exp list -> exp

val apply_closure : closure -> value list -> exp

val get_lets : declarations ->  (var * ty option * exp) list
  
val get_attr_type : declarations -> ty option

val get_merge : declarations -> exp option

val get_trans : declarations -> exp option

val get_init : declarations -> exp option

val get_assert : declarations -> exp option

val get_edges : declarations -> (Integer.t * Integer.t) list option

val get_nodes : declarations -> Integer.t option

val get_symbolics : declarations -> (var * ty_or_exp) list

val get_requires : declarations -> exp list

val equal_values : cmp_meta:bool -> value -> value -> bool

val equal_exps : cmp_meta:bool -> exp -> exp -> bool

val hash_value : hash_meta:bool -> value -> int

val hash_exp : hash_meta:bool -> exp -> int

(* Operates only on the 'v' element of the value records, ignoring
   all other entries *)
val compare_vs : value -> value -> int

(* As above, but for exps *)
val compare_es : exp -> exp -> int

(* Operates on all entries in the value records *)
val compare_values : value -> value -> int

(* As above, but for exps *)
val compare_exps : exp -> exp -> int

(* Actual equality. For equivalence, consider using
   Typing.equiv_tys instead *)
val equal_tys : ty -> ty -> bool

val show_exp : exp -> string

val get_inner_type : ty -> ty

val free : Var.t BatSet.PSet.t -> exp -> Var.t BatSet.PSet.t

val free_dead_vars : exp -> exp

val show_exp : show_meta:bool -> exp -> string

val show_value : show_meta:bool -> value -> string

val show_span: Span.t -> string

val show_ty: ty -> string

(** [get_ty_from_tyexp t] @return the type wrapped by [Ty] or the type
   of the expression wrapped by [Exp]. Fails if the expression has no
   type. *)
val get_ty_from_tyexp: ty_or_exp -> ty

val bool_of_val: value -> bool option

val proj_var: int -> var -> var

val default_exp_value: ty -> exp
  
module type MEMOIZER = sig
  type t

  val memoize : size:int -> (t -> 'a) -> t -> 'a
end

module MemoizeValue : MEMOIZER with type t = value

module MemoizeExp : MEMOIZER with type t = exp

module BddMap : sig
  type t = mtbdd

  val create : key_ty:ty -> value -> t

  val map :
    op_key:exp * value BatSet.PSet.t -> (value -> value) -> t -> t

  val map_when :
    op_key:exp * value BatSet.PSet.t
    -> bool Mtbdd.t
    -> (value -> value)
    -> t
    -> t

  val merge :
    ?opt:value * value * value * value
    -> op_key:exp * value BatSet.PSet.t
    -> (value -> value -> value)
    -> t
    -> t
    -> t

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

  val wrap_mtbdd : Bdd.vt -> bool Mtbdd.t
end

val default_value : ty -> value
