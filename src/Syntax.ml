(* Abstract syntax of SRP attribute processing expressions *)

open Unsigned

module type VAR =
sig
  type t
  val fresh : string -> t
  val name : t -> string
  val to_var : string * int -> t
  val from_var : t -> string * int
  val to_string : t -> string
  val equals : t -> t -> bool
  val compare : t -> t -> int
end
    
module Var : VAR =
struct
  type t = string * int

  let counter = ref (-1)
  let next () =
    counter := !counter + 1;
    !counter
    
  let fresh s = (s, next())
  let name (s,i) = s
  let to_var (s,i) = (s,i)
  let from_var (s,i) = (s,i)
  let to_string (s,i) = s ^ string_of_int i
  let equals (s1,i1) (s2,i2) = s1 = s2 && i1 = i2
  let compare (s1,i1) (s2,i2) =
    if s1 < s2 then -1
    else if s1 > s2 then 1
    else if i1 < i2 then -1
    else if i1 > i2 then 1
    else 0
end

type var = Var.t

module UIMap =
  Map.Make (
    struct
      type t = UInt32.t
      let compare = UInt32.compare
    end
  ) 
    
type value =
  | VBool of bool
  | VUInt32 of UInt32.t  
  | VMap of value UIMap.t
  | VTuple of value list
  | VOption of value option

type op =
  (* Equality of values *)
  | Eq
  (* Boolean operators *)
  | And
  | Or
  | Not
  (* Unsigned Integer 32 operators *)
  | UIncr
  | UAdd
  | ULessEq
  (* Map operations *)
  | MPresent
  | MGet
  | MBind  (* MBind [map; (k,value)] *)
  | MUnion

type exp =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EApp of var * exp list
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | EProj of int * exp
  | ESome of exp
  | EMatch of exp * exp * var * exp  (* match e1 with None -> e2 | Some v -> e3 *) 

(* n-ary top-level function *)      
type func = var list * exp

(* declaration *)
type decl =
  | DE of exp
  | DF of func

(* declaration sequence *)      
type decls = (var * decl) list
      
(* Utilities *)

let arity op =
  match op with
  | Eq -> 2
  | And -> 2
  | Or -> 2
  | Not -> 1
  | UIncr -> 1
  | UAdd -> 2
  | ULessEq -> 2
  | MPresent -> 2
  | MGet -> 2
  | MBind -> 2
  | MUnion -> 2

let rec equal_val v1 v2 =
  match v1, v2 with
    | VBool b1, VBool b2 -> b1 = b2
    | VUInt32 i1, VUInt32 i2 -> UInt32.compare i1 i2 = 0
    | VMap m1, VMap m2 -> UIMap.equal equal_val m1 m2
    | VTuple vs1, VTuple vs2 -> equal_vals vs1 vs2
    | VOption None, VOption None -> true
    | VOption (Some v1), VOption (Some v2) -> equal_val v1 v2
    | _, _ -> false
and equal_vals vs1 vs2 =
  match vs1, vs2 with
    | [], [] -> true
    | v1::rest1, v2::rest2 -> equal_val v1 v2 && equal_vals rest1 rest2
    | _, _ -> false

