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
  | VFun of func

and exp =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EApp of exp * exp list
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | EProj of int * exp
  | ESome of exp
  | EMatch of exp * exp * var * exp  (* match e1 with None -> e2 | Some v -> e3 *) 

and func = var list * exp
      
(* declaration sequence *)      
type decls = (var * exp) list
      
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
  | MCreate -> 1
  | MGet -> 2
  | MSet -> 3
  | MMap -> 2
  | MMerge -> 3

exception Equality
    
let rec equal_val v1 v2 =
  match v1, v2 with
    | VBool b1, VBool b2 -> b1 = b2
    | VUInt32 i1, VUInt32 i2 -> UInt32.compare i1 i2 = 0
    | VMap m1, VMap m2 -> IMap.equal equal_val m1 m2
    | VTuple vs1, VTuple vs2 -> equal_vals vs1 vs2
    | VOption None, VOption None -> true
    | VOption (Some v1), VOption (Some v2) -> equal_val v1 v2
    | VFun (vs1,e1), _ -> raise Equality
    | _, VFun(vs2,e2) -> raise Equality
    | _, _ -> false
and equal_vals vs1 vs2 =
  match vs1, vs2 with
    | [], [] -> true
    | v1::rest1, v2::rest2 -> equal_val v1 v2 && equal_vals rest1 rest2
    | _, _ -> false

