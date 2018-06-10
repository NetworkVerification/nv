(* Printing utilities for abstract syntax *)

open Unsigned
open Syntax
      
let op_to_string op =
    match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "!"
  | UAdd -> "+"
  | ULessEq -> "<="
  | UEq -> "="
  | SSingle -> "#"
  | SUnion -> "U"
  | SDiff -> "-"
  | SMember -> "?"

let max_prec = 10
  
let prec_op op =
  match op with
  | And -> 7
  | Or -> 7
  | Not -> 6
  | UAdd -> 3
  | ULessEq -> 5
  | UEq -> 5
  | SSingle -> 2
  | SUnion -> 3 
  | SDiff -> 3
  | SMember -> 4

let prec_exp e =
  match e with
    | EVar x -> 0
    | EVal v -> 0
    | EOp (op, _) -> prec_op op
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
      
let rec value_to_string_p prec v =
  match v with
    | VBool true -> "true"
    | VBool false -> "false"
    | VUInt32 i -> UInt32.to_string i
    | VSet s -> "{" ^ comma_sep UInt32.to_string  (UInt32Set.elements s) ^ "}"
    | VTuple vs -> "(" ^ comma_sep (value_to_string_p max_prec) vs ^ ")"
    | VOption None -> "None"
    | VOption (Some v) ->
      let s = "Some" ^ value_to_string_p max_prec v in
      if max_prec > prec then "(" ^ s ^ ")" else s
	
let rec exp_to_string_p prec e =
  let p = prec_exp e in
  let s =
    match e with
      | EVar x -> x
      | EVal v -> value_to_string_p prec v
      | EOp (op, []) -> op_to_string op
      | EOp (op, [e1]) -> op_to_string op ^ exp_to_string_p p e1
      | EOp (op, [e1;e2]) -> exp_to_string_p p e1 ^ " " ^ op_to_string op ^ " " ^ exp_to_string_p prec e2
      | EOp (op, es) -> op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
      | EIf (e1,e2,e3) ->
	"if " ^ exp_to_string_p max_prec e1 ^
	  " then " ^ exp_to_string_p max_prec e2 ^
	  " else " ^ exp_to_string_p prec e3
      | ELet (x,e1,e2) ->
	"let " ^ x ^ "=" ^ exp_to_string_p max_prec e1 ^
	  " in " ^ exp_to_string_p prec e2
      | ETuple es -> "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
      | EProj (i,e) -> (exp_to_string_p p e) ^ "." ^ string_of_int i
      | ESome e -> "Some " ^ exp_to_string_p prec e
      | EMatch (e1,e2,v,e3) ->
	"match " ^ exp_to_string_p max_prec e1 ^ " with " ^
	  "None -> (" ^ exp_to_string_p max_prec e2 ^ ")" ^
	  "Some " ^ v ^ " -> (" ^ exp_to_string_p max_prec e3 ^ ")"
  in
  if p > prec then "(" ^ s ^ ")" else s


let exp_to_string e = exp_to_string_p max_prec e
let value_to_string v = value_to_string_p max_prec v
