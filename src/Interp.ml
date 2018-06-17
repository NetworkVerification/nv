(* Interpreter for SRP attribute processing language *)

open Unsigned
open Syntax
open Printing
open Printf

(* Interpreter Errors *)

exception IError of string
let error s = raise (IError s)

(* Environments *)

module Env =
struct

  module M = Map.Make (Var)
	
  type t = value M.t

  let empty = M.empty
    
  let lookup env x =
    try
      M.find x env
    with
	Not_found -> error ("unbound variable " ^ Var.to_string x)
	
  let update env x entry =
    M.add x entry env

  let to_string env =
    M.fold (fun k v s -> Var.to_string k ^ "=" ^ value_to_string v ^ ";" ^ s) env
end
  
(* Expression and operator interpreters *)
    
let rec interp_exp env e =
  match e with
    | EVar x -> Env.lookup env x
    | EVal v -> v
    | EOp (op, es) -> interp_op env op es
    | EApp (e, es) ->
      let vs = List.map (interp_exp env) es in
      (match interp_exp env e with
	  VFun (xs,body) -> apply env (xs,body) vs
	| _ -> error "bad functional application")
    | EIf (e1, e2, e3) ->
      (match interp_exp env e1 with
	| VBool true -> interp_exp env e2
	| VBool false -> interp_exp env e3
	| _ -> error "bad if condition")
    | ELet (x,e1,e2) ->
      let v1 = interp_exp env e1 in
      interp_exp (Env.update env x v1) e2
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
	| VOption (Some v) -> interp_exp (Env.update env x v) e3
	| v -> error ("match expression processing non-option: " ^ value_to_string v))

and apply env (vars, body) vs =
  let rec create_env env vars vs =
    match vars, vs with
      | [], [] -> env
      | var::vars, v::vs -> create_env (Env.update env var v) vars vs
      | _, _ -> error "bad function application"
  in	
  interp_exp (create_env env vars vs) body 
	
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
    | UEq, [VUInt32 i1; VUInt32 i2] ->
        if UInt32.compare i1 i2 = 0 then
	  VBool true
        else
          VBool false
    | ULess, [VUInt32 i1; VUInt32 i2] ->
        if UInt32.compare i1 i2 = -1 then
  	  VBool true
        else
	  VBool false
    | MCreate, [VUInt32 i] -> VMap (IMap.create i)
    | MGet, [VMap m; VUInt32 i] -> VOption (IMap.get m i)
    | MSet, [VMap m; VUInt32 i; v] -> VMap (IMap.set m i v )
    | MMap, [VFun (vs,e); VMap m] -> VMap (IMap.map (fun v -> apply env (vs,e) [v]) m)
    | MMerge, [VFun (vs,e); VMap m1; VMap m2] ->
      let f_lifted v1opt v2opt =
	match apply env (vs,e) [VOption v1opt; VOption v2opt] with
	  | VOption vopt -> vopt
	  | _ -> error "bad merge application; did not return option value"
      in
      VMap (IMap.merge f_lifted m1 m2)
    | _, _ -> error "bad operator application"

let interp e = interp_exp Env.empty e
  
let interp_decls ds =
  let rec loop env ds =
    match ds with
	[] -> env
      | (x,e)::ds ->
	Env.update env x (interp_exp env e)
  in
  loop Env.empty ds
