(* Printing utilities for abstract syntax *)

open Unsigned
open Syntax
      
let op_to_string op =
    match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "!"
  | UAdd -> "+" 
  | USub -> "-"
  | UEq -> "="
  | ULess -> "<="
  | MCreate -> "create"
  | MGet -> "!"
  | MSet -> "set"
  | MMap -> "map"
  | MMerge -> "merge"

let is_keyword_op op =
     match op with
  | And | Or | Not | UAdd | USub | UEq | ULess | MGet -> false
  | MCreate | MSet | MMap | MMerge -> true
    
let max_prec = 10
  
let prec_op op =
  match op with
    | And -> 7
    | Or -> 7
    | Not -> 6
    | UAdd -> 4
    | USub -> 4
    | UEq -> 5
    | ULess -> 5
    | MCreate -> 5
    | MGet -> 5
    | MSet -> 3
    | MMap -> 5
    | MMerge -> 5

let prec_exp e =
  match e with
    | EVar _ -> 0
    | EVal _ -> 0
    | EOp (op, _) -> prec_op op
    | EApp _ -> max_prec  
    | EIf _ -> max_prec
    | ELet _ -> max_prec
    | ETuple _ -> 0
    | EProj _ -> 1
    | ESome _ -> max_prec
    | EMatch _ -> 0
      

let rec sep s f xs =
  match xs with
    | [] -> ""
    | [x] -> f x
    | x::y::rest -> f x ^ s ^ sep s f (y::rest)

let comma_sep f xs = sep "," f xs

let rec func_to_string_p prec (xs,e) =
  let s = "\\" ^ comma_sep Var.to_string xs ^  "." ^ exp_to_string_p max_prec e in
  if prec < max_prec then
    "(" ^ s ^ ")"
  else
    s
  
and value_to_string_p prec v =
  match v with
    | VBool true -> "true"
    | VBool false -> "false"
    | VUInt32 i -> UInt32.to_string i
    | VMap m ->
      let binding_to_string (k,v) =
	UInt32.to_string k ^ ":" ^
	  value_to_string_p max_prec v
      in
      "{" ^ comma_sep binding_to_string (IMap.bindings m) ^ "}"
    | VTuple vs -> "(" ^ comma_sep (value_to_string_p max_prec) vs ^ ")"
    | VOption None -> "None"
    | VOption (Some v) ->
      let s = "Some" ^ value_to_string_p max_prec v in
      if max_prec > prec then "(" ^ s ^ ")" else s
    | VFun (vs,e) -> func_to_string_p prec (vs,e)
	
and exp_to_string_p prec e =
  let p = prec_exp e in
  let s =
    match e with
      | EVar x -> Var.to_string x
      | EVal v -> value_to_string_p prec v
      | EOp (op, es) -> op_args_to_string prec p op es
      | EApp (e, es) ->
	exp_to_string_p max_prec e ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
      | EIf (e1,e2,e3) ->
	"if " ^ exp_to_string_p max_prec e1 ^
	  " then " ^ exp_to_string_p max_prec e2 ^
	  " else " ^ exp_to_string_p prec e3
      | ELet (x,e1,e2) ->
	"let " ^ Var.to_string x ^ "=" ^ exp_to_string_p max_prec e1 ^
	  " in " ^ exp_to_string_p prec e2
      | ETuple es -> "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
      | EProj (i,e) -> (exp_to_string_p p e) ^ "." ^ string_of_int i
      | ESome e -> "Some " ^ exp_to_string_p prec e
      | EMatch (e1,e2,v,e3) ->
	"match " ^ exp_to_string_p max_prec e1 ^ " with " ^
	  "None -> (" ^ exp_to_string_p max_prec e2 ^ ")" ^
	  "Some " ^ Var.to_string v ^ " -> (" ^ exp_to_string_p max_prec e3 ^ ")"
  in
  if p > prec then "(" ^ s ^ ")" else s

and op_args_to_string prec p op es =
  if is_keyword_op op then
    op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
  else
    (match es with
	[] -> op_to_string op ^ "()"  (* should not happen *)
      | [e1] -> op_to_string op ^ exp_to_string_p p e1
      | [e1;e2] ->
	exp_to_string_p p e1 ^ " " ^ op_to_string op ^ " " ^
	  exp_to_string_p prec e2
      | es ->
	op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
    )
      
let value_to_string v =
  value_to_string_p max_prec v

let exp_to_string e =
  exp_to_string_p max_prec e

let rec decls_to_string ds =
  match ds with
    | [] -> ""
    | (x,d)::ds ->
      "let " ^ Var.to_string x ^ "=" ^ exp_to_string d ^ "\n" ^ decls_to_string ds
