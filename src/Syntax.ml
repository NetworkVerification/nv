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

type v =
  | VBool of bool
  | VUInt32 of UInt32.t
  | VMap of value IMap.t * ty option
  | VTuple of value list
  | VOption of value option * ty option
  | VClosure of closure
  | VTyClosure of tyclosure

and value = {v: v; vty: ty option; vspan: Span.t option}

and e =
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

and exp = {e: e; ety: ty option; espan: Span.t option}

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

let exp (e : e) : exp = {e=e; ety=None; espan=None}

let value (v : v) : value = {v=v; vty=None; vspan=None}

let e_val (x: v) : exp = exp (EVal (value x))

exception Syntax of string

let error s = raise (Syntax s)

let func x body = {arg= x; argty= None; resty= None; body}

let ty_func tyargs body = (tyargs, body)

let lam x body = exp (EFun (func x body))

let rec lams params body =
  match params with
  | [] -> error "lams: no parameters"
  | [p] -> lam p body
  | p :: params -> lam p (lams params body)


let rec apps f args : exp =
  match args with
  | [] -> error "apps: no arguments"
  | [a] -> exp (EApp (f, a))
  | a :: args -> apps (exp (EApp (f, a))) args


let apply_closure cl (args : value list) =
  apps (e_val (VClosure cl)) (List.map (fun a -> exp (EVal a)) args)

let get_attr_type ds = 
  try 
  let daty = List.find (fun d -> 
    match d with
    | DATy ty -> true
    | _ -> false
  ) ds in 
  match daty with 
  | DATy ty -> Some ty 
  | _ -> failwith "impossible"
  with _ -> None