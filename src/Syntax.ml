(* Abstract syntax of SRP attribute processing expressions *)

open Unsigned

(* indices into maps or map sizes must be static constants *)
type index = UInt32.t

(* see:  http://okmij.org/ftp/ML/generalization.html *)
type level = int

type tyname = Var.t

type ty =
  | TVar of tyvar ref
  (* schematic variable to be unified *)
  | QVar of tyname
  (* prenex quantified variable *)
  | TBool
  | TInt of index
  (* index is number of bits in Int type: 32 for now *)
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of index * ty
  (* TMap (i,t) is a map from [0..i-1] to t *)
  | TAll of tyname list * ty

and tyvar = Unbound of tyname * level | Link of ty

type var = Var.t

type op =
  (* Boolean operators *)
  | And
  | Or
  | Not
  (* Unsigned Integer 32 operators *)
  | UAdd
  | USub
  | UEq
  | ULess
  | ULeq
  (* Map operations *)
  | MCreate of ty option
  (* MCreate n -- creates map 0..n-1 with type ty *)
  | MGet
  (* MGet m k = m[k] *)
  | MSet
  (* MStore m k v = m[k]:=v *)
  | MMap
  (* MMap f m = [f m[0]; f m[1]; ...] *)
  | MMerge

(* MMerge f m1 m2 = [f m1[0] m2[0]; ... ] *)

type pattern =
  | PWild
  | PVar of var
  | PBool of bool
  | PUInt32 of UInt32.t
  | PTuple of pattern list
  | POption of pattern option

type value =
  | VBool of bool
  | VUInt32 of UInt32.t
  | VMap of value IMap.t * ty option
  | VTuple of value list
  | VOption of value option * ty option
  | VClosure of closure
  | VTyClosure of tyclosure

and exp =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | ETyFun of tyfunc
  | EApp of exp * exp
  | ETyApp of exp * ty list
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | EProj of int * exp
  | ESome of exp
  | EMatch of exp * branches
  | ETy of exp * ty

and branches = (pattern * exp) list

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and tyfunc = (tyname list * exp)

and closure = (env * func)

and tyclosure = (env * tyfunc)

and env = {ty: ty Env.t; value: value Env.t}

type declaration =
  | DLet of var * exp
  | DATy of ty
  | DMerge of exp
  | DTrans of exp
  | DNodes of UInt32.t
  | DEdges of (UInt32.t * UInt32.t) list
  | DInit of exp

type declarations = declaration list

(* Utilities *)

let arity op =
  match op with
  | And -> 2
  | Or -> 2
  | Not -> 1
  | UAdd -> 2
  | USub -> 2
  | UEq -> 2
  | ULess -> 2
  | ULeq -> 2
  | MCreate _ -> 2
  | MGet -> 2
  | MSet -> 3
  | MMap -> 2
  | MMerge -> 3


(* Useful constructors *)

let ( ~> ) ty ty = TArrow (ty, ty)

let tint = TInt (UInt32.of_int 32)

let exp v = EVal v

exception Syntax of string

let error s = raise (Syntax s)

let func x body = {arg= x; argty= None; resty= None; body}

let ty_func tyargs body = (tyargs, body)

let lam x body = EFun (func x body)

let rec lams params body =
  match params with
  | [] -> error "lams: no parameters"
  | [p] -> lam p body
  | p :: params -> lam p (lams params body)


let rec apps f args =
  match args with
  | [] -> error "apps: no arguments"
  | [a] -> EApp (f, a)
  | a :: args -> apps (EApp (f, a)) args


let apply_closure cl args =
  apps (EVal (VClosure cl)) (List.map (fun a -> exp a) args)
