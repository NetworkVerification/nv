(* Interpreter for SRP attribute processing language *)

open Unsigned
open Syntax
open Printing
open Printf

(* Interpreter Errors *)

exception IError of string
let error s = raise (IError s)

(* Equality of values *)

exception Equality of value
    
let rec equal_val v1 v2 =
  match v1, v2 with
    | VBool b1, VBool b2 -> b1 = b2
    | VUInt32 i1, VUInt32 i2 -> UInt32.compare i1 i2 = 0
    | VMap m1, VMap m2 -> IMap.equal equal_val m1 m2
    | VTuple vs1, VTuple vs2 -> equal_vals vs1 vs2
    | VOption None, VOption None -> true
    | VOption (Some v1), VOption (Some v2) -> equal_val v1 v2
    | VClosure (x1,e1), _ -> raise (Equality v1)
    | _, VClosure(x2,e2) -> raise (Equality v2)
    | _, _ -> false
and equal_vals vs1 vs2 =
  match vs1, vs2 with
    | [], [] -> true
    | v1::rest1, v2::rest2 -> equal_val v1 v2 && equal_vals rest1 rest2
    | _, _ -> false
  
(* Expression and operator interpreters *)
    
let rec interp_exp env e =
  match e with
    | EVar x -> Env.lookup env x
    | EVal v -> v
    | EOp (op, es) -> interp_op env op es
    | EFun (v,e) -> VClosure (env, (v,e))
    | EApp (e1, e2) ->
      let v1 = interp_exp env e1 in
      let v2 = interp_exp env e2 in
      (match v1 with
	  VClosure (c_env, (x, body)) -> interp_exp (Env.update c_env x v2) body
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
    | MCreate, [VUInt32 i; v] -> VMap (IMap.create i v)
    | MGet, [VMap m; VUInt32 i] ->
      (try
	IMap.find m i
       with IMap.Out_of_bounds i -> error ("bad get: " ^ UInt32.to_string i))
    | MSet, [VMap m; VUInt32 i; v] -> VMap (IMap.update m i v )
    | MMap, [VClosure (c_env, (x,e)); VMap m] -> VMap (IMap.map (fun v -> apply c_env (x,e) v) m)
    | MMerge, [VClosure (c_env, (x,e)); VMap m1; VMap m2] ->
      let f_lifted v1opt v2opt =
	match apply c_env (x,e) (VTuple [VOption v1opt; VOption v2opt]) with
	  | VOption vopt -> vopt
	  | _ -> error "bad merge application; did not return option value"
      in
      VMap (IMap.merge f_lifted m1 m2)
    | _, _ -> error "bad operator application"

and apply env (x, body) v =	
  interp_exp (Env.update env x v) body 

  
let interp e = interp_exp Env.empty e

let interp_env env e = interp_exp env e

let interp_closure cl args = interp (Syntax.apply_closure cl args)
