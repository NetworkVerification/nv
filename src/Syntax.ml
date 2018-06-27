(* Abstract syntax of SRP attribute processing expressions *)

open Unsigned

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
  | MCreate (* MCreate n -- creates map 0..n-1 *)
  | MGet    (* MGet m k = m[k] *)
  | MSet    (* MStore m k v = m[k]:=v *)
  | MMap    (* MMap f m = [f m[0]; f m[1]; ...] *)
  | MMerge  (* MMerge f m1 m2 = [f m1[0] m2[0]; ... ] *)

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
  | VMap of value IMap.t
  | VTuple of value list
  | VOption of value option
  | VClosure of closure

and exp =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | EProj of int * exp
  | ESome of exp
  | EMatch of exp * branches

and branches = (pattern * exp) list

and func = var * exp

and closure = value Env.t * func

type declaration =
  | DLet of var * exp
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
  | MCreate -> 2
  | MGet -> 2
  | MSet -> 3
  | MMap -> 2
  | MMerge -> 3

(* Useful constructors *)

let exp v = EVal v

exception Syntax of string
let error s = raise (Syntax s)

let rec lams params body =
  match params with
      [] -> error "lams: no parameters"
    | [p] -> EFun (p,body)
    | p::params -> EFun (p, lams params body)
      
let rec apps f args =
  match args with
      [] -> error "apps: no arguments"
    | [a] -> EApp(f,a)
    | a::args -> apps (EApp (f,a)) args

let apply_closure cl args = apps (EVal (VClosure cl)) (List.map (fun a -> exp a) args)
