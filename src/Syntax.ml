(* Abstract syntax of SRP attribute processing expressions *)

open Unsigned

module UInt32Set =
  Set.Make (
    struct
      type t = UInt32.t
      let compare = UInt32.compare
    end
  )
  
type value =
  | VBool of bool
  | VUInt32 of UInt32.t  
  | VSet of UInt32Set.t
  | VTuple of value list
  | VOption of value option

type op =
  (* Boolean operators *)
  | And
  | Or
  | Not
  (* Unsigned Integer 32 operators *)
  | UAdd
  | ULessEq
  | UEq
  (* Set operations *)
  | SSingle
  | SUnion
  | SDiff
  | SMember

type var = string

type exp =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | EProj of int * exp
  | ESome of exp
  | EMatch of exp * exp * var * exp  (* match e1 with None -> e2 | Some v -> e3 *) 

(* n-ary top-level function *)      
type func = var list * exp      
      
(* Utilities *)

let arity op =
  match op with
  | And -> 2
  | Or -> 2
  | Not -> 1
  | UAdd -> 2
  | ULessEq -> 2
  | UEq -> 2
  | SSingle -> 1
  | SUnion -> 2
  | SDiff -> 2
  | SMember -> 2

let rec equal_val v1 v2 =
  match v1, v2 with
    | VBool b1, VBool b2 -> b1 = b2
    | VUInt32 i1, VUInt32 i2 -> UInt32.compare i1 i2 = 0
    | VSet s1, VSet s2 -> UInt32Set.equal s1 s2
    | VTuple vs1, VTuple vs2 -> equal_vals vs1 vs2
    | VOption None, VOption None -> true
    | VOption (Some v1), VOption (Some v2) -> equal_val v1 v2
    | _, _ -> false
and equal_vals vs1 vs2 =
  match vs1, vs2 with
    | [], [] -> true
    | v1::rest1, v2::rest2 -> equal_val v1 v2 && equal_vals rest1 rest2
    | _, _ -> false

