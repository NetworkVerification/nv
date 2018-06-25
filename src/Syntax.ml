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
  | EMatch of exp * exp * var * exp  (* match e1 with None -> e2 | Some v -> e3 *) 

and func = var * exp

and closure = value Env.t * func

type declaration =
  | DLet of var * exp
  | DMerge of exp
  | DTrans of exp
  | DNodes of UInt32.t
  | DEdges of (UInt32.t * UInt32.t) list
  | DInit of (UInt32.t * exp) list

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
