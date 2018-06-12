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

  type entry =
    | V of value
    | F of func

  module M = Map.Make (Syntax.Var)
	
  type t = entry M.t

  let empty = M.empty
    
  let lookup env x =
    try
      M.find x env
    with
	Not_found -> error ("unbound variable " ^ Var.to_string x)

  let lookup_val env x =
    match lookup env x with
      | V v -> v
      | F f -> error ("lookup val found function" ^ Var.to_string x)

  let lookup_fun env x =
    match lookup env x with
      | V v -> error ("lookup function found val" ^ Var.to_string x)
      | F f -> f
	
  let update env x entry =
    M.add x entry env

  let update_val env x v =
    update env x (V v)

  let update_fun env x f =
    update env x (F f)

  let to_string env =
    M.fold (fun k entry s ->
      let entry_string = 
	match entry with
	  | V v -> value_to_string v
	  | F f -> func_to_string f
      in
      Var.to_string k ^ ":" ^ entry_string ^ ";" ^ s) env
end
  
(* Expression and operator interpreters *)
    
let rec interp_exp env e =
  match e with
    | EVar x -> Env.lookup_val env x
    | EVal v -> v
    | EOp (op, es) -> interp_op env op es
    | EApp (x, es) ->
      let vs = List.map (interp_exp env) es in
      let f = Env.lookup_fun env x in
      apply f vs
    | EIf (e1, e2, e3) ->
      (match interp_exp env e1 with
	| VBool true -> interp_exp env e2
	| VBool false -> interp_exp env e3
	| _ -> error "bad if condition")
    | ELet (x,e1,e2) ->
      let v1 = interp_exp env e1 in
      interp_exp (Env.update_val env x v1) e2
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
	| VOption (Some v) -> interp_exp (Env.update_val env x v) e3
	| _ -> error "match expression processing non-option")

and apply (vars, body) vs =
  let rec create_env env vars vs =
    match vars, vs with
      | [], [] -> env
      | var::vars, v::vs -> create_env (Env.update_val env var v) vars vs
      | _, _ -> error "bad function application"
  in	
  interp_exp (create_env Env.empty vars vs) body 
	
and interp_op env op es =
  if arity op != List.length es then
    error (sprintf "operation %s has arity %d not arity %d"
	     (op_to_string op) (arity op) (List.length es));
  let vs = List.map (interp_exp env) es in
  match op, vs with
    | Eq, [v1; v2] ->
        if equal_val v1 v2 then
	  VBool true
        else
          VBool false
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
    | MPresent, [VMap m; VUInt32 i] ->
        VBool (UIMap.mem i m)
    | MGet, [VMap m; VUInt32 i] ->
      (try
	 VOption (Some (UIMap.find i m))
       with
	   Not_found -> VOption None)
    | MBind, [VMap m; VTuple [VUInt32 i; v]] ->
        VMap (UIMap.add i v m)
    | MUnion,  [VMap m1; VMap m2] ->  error "UNIMPLEMENTED"  (* TODO *)
        (* need ocaml 4.03: VBool (UI2Map.union (fun k v1 v2 -> v1) m1 m2) *)
    | _, _ ->
        error "bad operator application"

let interp e = interp_exp Env.empty e

let interp_decl env d =
  match d with
    | DE e -> Env.V (interp_exp env e)
    | DF f -> Env.F f
  
let interp_decls ds =
  let rec loop env ds =
    match ds with
	[] -> env
      | (x,d)::ds ->
	let entry = interp_decl env d in
	Env.update env x entry                             (* inefficient *)
  in
  loop Env.empty ds
