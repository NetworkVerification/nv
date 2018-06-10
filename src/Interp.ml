(* Interpreter for SRP attribute processing language *)

open Unsigned
open Syntax
open Printing
open Printf

(* Interpreter Errors *)

exception IError of string
let error s = raise (IError s)

(* Environments *)

module StringMap = Map.Make (
  struct
    type t = string
    let compare s1 s2 = Pervasives.compare s1 s2
  end
)  
  
type env = value StringMap.t

let empty = StringMap.empty
    
let lookup env x =
  try
    StringMap.find x env
  with
      Not_found -> error ("unbound variable " ^ x)

let update env x v =
  StringMap.add x v env

let env_to_string env =
  StringMap.fold (fun k v s -> k ^ ":" ^ value_to_string v ^ ";" ^ s) env

(* Expression and operator interpreters *)
    
let rec interp_exp env e =
  match e with
    | EVar x -> lookup env x
    | EVal v -> v
    | EOp (op, es) -> interp_op env op es
    | EIf (e1, e2, e3) ->
      (match interp_exp env e1 with
	| VBool true -> interp_exp env e2
	| VBool false -> interp_exp env e3
	| _ -> error "bad if condition")
    | ELet (x,e1,e2) ->
      let v1 = interp_exp env e1 in
      interp_exp (update env x v1) e2
    | ETuple es -> VTuple (List.map (interp_exp env) es)
    | EProj (i,e) ->
      (if i < 0 then error (sprintf "negative projection from tuple: %d " i);
       match interp_exp env e with
	 | VTuple vs ->
	   (if i >= List.length vs then
	       error (sprintf "projection out of range: %d > %d" i (List.length vs));
	    List.nth vs i)
	 | _ -> error ("bad projection"))
    | ESome e -> VOption (Some (interp_exp env e))
    | EMatch (e1,e2,x,e3) ->
      (match interp_exp env e1 with
	| VOption None -> interp_exp env e2
	| VOption (Some v) -> interp_exp (update env x v) e3
	| _ -> error "match expression processing non-option")
	       
and interp_op env op es =
  if arity op != List.length es then
    error (sprintf "operation %s has arity %d not arity %d"
	     (op_to_string op) (arity op) (List.length es));
  let vs = List.map (interp_exp env) es in
  match op, vs with
    | And, [VBool b1; VBool b2] ->
        VBool (b1 && b2)
    | Or, [VBool b1; VBool b2] ->
        VBool (b1 || b2)
    | Not, [VBool b1] ->
        VBool (not b1)
    | UAdd, [VUInt32 i1; VUInt32 i2] ->
        VUInt32 (UInt32.add i1 i2)
    | ULessEq, [VUInt32 i1; VUInt32 i2] ->
        if UInt32.compare i1 i2 = -1 || UInt32.compare i1 i2 = 0 then
  	  VBool true
        else
	  VBool false
    | UEq, [VUInt32 i1; VUInt32 i2] ->
        if UInt32.compare i1 i2 = 0 then
	  VBool true
        else
          VBool false
    | SSingle, [VUInt32 i] ->
        VSet (UInt32Set.singleton i)
    | SUnion, [VSet s1; VSet s2] ->
	VSet (UInt32Set.union s1 s2)
    | SDiff, [VSet s1; VSet s2] ->
        VSet (UInt32Set.diff s1 s2)
    | SMember,  [VUInt32 i; VSet s] ->
        VBool (UInt32Set.mem i s)
    | _, _ ->
        error "bad operator application"

let interp e = interp_exp empty e

let apply (vars, body) vs =
  let rec create_env e vars vs =
    match vars, vs with
      | [], [] -> e
      | var::vars, v::vs -> create_env (update e var v) vars vs
      | _, _ -> error "bad top-level functional application"
  in	
  interp_exp (create_env empty vars vs) body 
