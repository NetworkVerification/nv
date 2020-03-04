open Cudd
open Nv_datastructures
open Nv_utils.PrimitiveCollections

type node = int

val tnode_sz : int

type edge = node * node

type bitwidth = int

type level = int

type var = Var.t

type tyname = Var.t

type ty =
  | TVar of tyvar ref
  | QVar of tyname
  | TUnit
  | TBool
  | TInt of bitwidth
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty
  | TRecord of ty StringMap.t
  | TNode
  | TEdge

and tyvar = Unbound of tyname * level | Link of ty

type op =
  | And
  | Or
  | Not
  | Eq
  | UAdd of bitwidth
  | USub of bitwidth
  | ULess of bitwidth
  | ULeq of bitwidth
  | NLess
  | NLeq
  | AtMost of int
  | TGet of int (* Tuple size *) * int (* lo index *) * int (* hi index *)
  | TSet of int (* TUple size *) * int (* lo index *) * int (* hi index *)
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMapFilter
  | MMapIte
  | MMerge
  | MFoldNode
  | MFoldEdge
[@@deriving show]

type pattern =
  | PWild
  | PVar of var
  | PUnit
  | PBool of bool
  | PInt of Integer.t
  | PTuple of pattern list
  | POption of pattern option
  | PRecord of pattern StringMap.t
  | PNode of node
  | PEdge of pattern * pattern

module Pat : Map.OrderedType with type t = pattern

module PatMap : BatMap.S with type key = Pat.t

type v = private
  | VUnit
  | VBool of bool
  | VInt of Integer.t
  | VMap of mtbdd
  | VTuple of value list
  | VOption of value option
  | VClosure of closure
  | VRecord of value StringMap.t
  | VNode of node
  | VEdge of edge

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
  | ERecord of exp StringMap.t
  | EProject of exp * string

and exp = private
  {e: e; ety: ty option; espan: Span.t; etag: int; ehkey: int}

and branches

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and closure = env * func

and env = {ty: ty Env.t; value: value Env.t}

and ty_or_exp = Ty of ty | Exp of exp

val is_irrefutable : pattern -> bool

type branchLookup = Found of exp | Rest of (pattern * exp) list

val addBranch: Pat.t -> exp -> branches -> branches
val mapBranches: (Pat.t * exp -> Pat.t * exp) -> branches -> branches
val iterBranches: (Pat.t * exp -> unit) -> branches -> unit
val foldBranches: (PatMap.key * exp -> 'a -> 'a) -> 'a -> branches -> 'a
val lookUpPat: PatMap.key -> branches -> branchLookup

(** Raises not found *)
val popBranch: branches -> ((Pat.t * exp) * branches)
val emptyBranch : branches
val isEmptyBranch: branches -> bool
val optimizeBranches: branches -> branches
val branchToList: branches -> (PatMap.key * exp) list
val branchSize: branches -> unit

(* var_names should be an exp that uses only the EVar and ETuple constructors *)
type solve = {aty: ty option; var_names: exp; init : exp; trans: exp; merge: exp}

type declaration =
  | DLet of var * ty option * exp
  | DSymbolic of var * ty_or_exp
  | DATy of ty (* Declaration of the attribute type *)
  | DUserTy of var * ty (* Declaration of a record type *)
  | DMerge of exp
  | DTrans of exp
  | DInit of exp
  | DAssert of exp
  | DSolve of solve
  | DRequire of exp
  | DPartition of exp (* partition ids *)
  | DInterface of exp (* interface hypotheses *)
  | DNodes of int
  | DEdges of (node * node) list

type declarations = declaration list

type network =
  { attr_type    : ty;
    init         : exp;
    trans        : exp;
    merge        : exp;
    assertion    : exp option;
    solves       : solve list;
    partition    : exp option; (* partitioning *)
    interface    : exp option; (* partitioning *)
    symbolics    : (var * ty_or_exp) list;
    defs         : (var * ty option * exp) list;
    utys         : (var * ty) list;
    requires     : exp list;
    graph        : AdjGraph.t;
  }

(* TODO: add partitioning? *)
type srp_unfold =
  { srp_attr : ty;
    srp_constraints : exp AdjGraph.VertexMap.t;
    srp_labels : (var * ty) list AdjGraph.VertexMap.t;
    srp_symbolics : (var * ty_or_exp) list;
    srp_assertion : exp option;
    srp_requires : exp list;
    srp_graph : AdjGraph.t
  }

(* Constructors *)
val vunit : unit -> value

val vbool : bool -> value

val vnode : node -> value

val vedge : edge -> value

val vint : Integer.t -> value

val vmap : mtbdd -> value

val vtuple : value list -> value

val vrecord : value StringMap.t -> value

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

val erecord : exp StringMap.t -> exp

val eproject : exp -> string -> exp

val esome : exp -> exp

val ematch : exp -> branches -> exp

val ety : exp -> ty -> exp

val deconstructFun: exp -> func

val exp_to_pattern: exp -> pattern

(* exp must be a literal *)
val exp_to_value: exp -> value

val empty_env: env

(* Utilities *)

val arity : op -> int

val tupleToList : exp -> exp list

val tupleToListSafe : exp -> exp list

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

val update_value : env -> Var.t -> value -> env

val update_env: env -> Var.t -> value -> ty -> env

val lams : var list -> exp -> exp

val apps : exp -> exp list -> exp

val apply_closure : closure -> value list -> exp

val get_lets : declarations ->  (var * ty option * exp) list

val get_attr_type : declarations -> ty option

val get_merge : declarations -> exp option

val get_trans : declarations -> exp option

val get_init : declarations -> exp option

val get_asserts : declarations -> exp list

val get_solves : declarations -> solve list

val get_partition : declarations -> exp option

val get_interface : declarations -> exp option

val get_edges : declarations -> (node * node) list option

val get_nodes : declarations -> int option

val get_graph : declarations -> AdjGraph.t option

val get_symbolics : declarations -> (var * ty_or_exp) list

val get_requires : declarations -> exp list

val get_types : declarations -> (var * ty) list

val get_record_types : declarations -> (ty StringMap.t) list

val get_record_types_from_utys: (var * ty) list -> (ty StringMap.t) list

val equal_values : cmp_meta:bool -> value -> value -> bool

val equal_exps : cmp_meta:bool -> exp -> exp -> bool

val hash_value : hash_meta:bool -> value -> int

val hash_exp : hash_meta:bool -> exp -> int

val hash_ty : ty -> int

(* Operates only on the 'v' element of the value records, ignoring
   all other entries *)
val compare_vs : value -> value -> int

(* As above, but for exps *)
val compare_es : exp -> exp -> int

(* Operates on all entries in the value records *)
val compare_values : value -> value -> int

(* As above, but for exps *)
val compare_exps : exp -> exp -> int

val get_inner_type : ty -> ty

(* Actual equality. Prefer equal_inner_tys since it ignores TVar Links.
   For a stronger notion of equivalence, use Typing.equiv_tys *)
val equal_tys : ty -> ty -> bool

val equal_inner_tys : ty -> ty -> bool

val free : Var.t BatSet.PSet.t -> exp -> Var.t BatSet.PSet.t

val free_ty : Var.t BatSet.PSet.t -> exp -> (Var.t * ty) BatSet.PSet.t

val free_dead_vars : exp -> exp

(** [get_ty_from_tyexp t] @return the type wrapped by [Ty] or the type
    of the expression wrapped by [Exp]. Fails if the expression has no
    type. *)
val get_ty_from_tyexp: ty_or_exp -> ty

val bool_of_val: value -> bool option

val proj_var: int -> var -> var

val unproj_var: var -> (int * var)

val createNetwork: declarations -> network
