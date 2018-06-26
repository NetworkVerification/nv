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
  | ULess -> "<"
  | ULeq -> "<="
  | MCreate -> "create"
  | MGet -> "!"
  | MSet -> "set"
  | MMap -> "map"
  | MMerge -> "merge"

let is_keyword_op op =
     match op with
       | And | Or | Not | UAdd | USub | UEq | ULess | ULeq | MGet -> false
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
    | ULeq -> 5
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
    | EFun _ -> max_prec
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

let rec term s f xs =
  match xs with
    | [] -> ""
    | x::rest -> f x ^ s ^ sep s f rest

let comma_sep f xs = sep "," f xs
let semi_sep f xs = sep ";" f xs
let semi_term f xs = term ";" f xs
  
let rec func_to_string_p prec (x,e) =
  let s = "fun " ^ Var.to_string x ^  " -> " ^ exp_to_string_p max_prec e in
  if prec < max_prec then
    "(" ^ s ^ ")"
  else
    s

and closure_to_string_p prec (env, (x,e)) =
  let s = "fun[" ^ Env.to_string (value_to_string_p max_prec) env ^ "]\n" ^ Var.to_string x ^  " -> " ^ exp_to_string_p max_prec e in
  if prec < max_prec then
    "(" ^ s ^ ")"
  else
    s      
      
and map_to_string sep_s term_s m =
  let binding_to_string (k,v) = UInt32.to_string k ^ sep_s ^ value_to_string_p max_prec v in
  let (bs,default) = IMap.bindings m in
  "{" ^ term term_s binding_to_string bs ^ "default" ^ sep_s ^ value_to_string_p max_prec default ^ term_s ^ "}"
      
and value_to_string_p prec v =
  match v with
    | VBool true -> "true"
    | VBool false -> "false"
    | VUInt32 i -> UInt32.to_string i
    | VMap m -> map_to_string "=" ";" m
    | VTuple vs -> "(" ^ comma_sep (value_to_string_p max_prec) vs ^ ")"
    | VOption None -> "None"
    | VOption (Some v) ->
      let s = "Some" ^ value_to_string_p max_prec v in
      if max_prec > prec then "(" ^ s ^ ")" else s
    | VClosure (vs,f) -> closure_to_string_p prec (vs, f)
	
and exp_to_string_p prec e =
  let p = prec_exp e in
  let s =
    match e with
      | EVar x -> Var.to_string x
      | EVal v -> value_to_string_p prec v
      | EOp (op, es) -> op_args_to_string prec p op es
      | EFun (x,e) -> "\\" ^ Var.to_string x ^ "." ^ exp_to_string_p prec e
      | EApp (e1, e2) ->
	exp_to_string_p prec e1 ^ " " ^ exp_to_string_p prec e2 ^ " "
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
	  "none -> (" ^ exp_to_string_p max_prec e2 ^ ")" ^
	  "some " ^ Var.to_string v ^ " -> (" ^ exp_to_string_p max_prec e3 ^ ")"
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

let func_to_string f =
  func_to_string_p max_prec f

let closure_to_string c =
  closure_to_string_p max_prec c

let rec declaration_to_string d =
  match d with
    | DLet (x,e) -> "let " ^ Var.to_string x ^ " = " ^ exp_to_string e 
    | DMerge e -> "let merge = " ^ exp_to_string e 
    | DTrans e -> "let trans = " ^ exp_to_string e 
    | DNodes n -> "let nodes = " ^ UInt32.to_string n
    | DEdges es ->
      "let edges = {"
      ^ List.fold_right (fun (u,v) s -> UInt32.to_string u ^ "=" ^ UInt32.to_string v ^ ";") es ""
      ^ "}"
    | DInit (es,e) ->
      "let init = {"
      ^ List.fold_right (fun (u,e) s -> UInt32.to_string u ^ "=" ^ exp_to_string e ^ ";") es ""
      ^ "default=" ^ exp_to_string e ^ ";}"
	
let rec declarations_to_string ds =
  match ds with
    | [] -> ""
    | d::ds -> declaration_to_string d ^ "\n" ^ declarations_to_string ds
