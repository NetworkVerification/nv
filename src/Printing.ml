(* Printing utilities for abstract syntax *)

open Unsigned
open Syntax

let is_keyword_op op =
  match op with
  | And | Or | Not | UAdd | USub | UEq | ULess | ULeq | MGet -> false
  | MCreate | MSet | MMap | MMerge | MFilter -> true

(* set to true if you want to print universal quanifiers explicitly *)
let quantifiers = true

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
  | MFilter -> 5

let prec_exp e =
  match e.e with
  | EVar _ -> 0
  | EVal _ -> 0
  | EOp (op, _) -> prec_op op
  | EFun _ -> 8
  | EApp _ -> max_prec
  | EIf _ -> max_prec
  | ELet _ -> max_prec
  | ETuple _ -> 0
  | ESome _ -> max_prec
  | EMatch _ -> 8
  | ETy (_, _) -> max_prec

let rec sep s f xs =
  match xs with
  | [] -> ""
  | [x] -> f x
  | x :: y :: rest -> f x ^ s ^ sep s f (y :: rest)

let rec term s f xs =
  match xs with [] -> "" | x :: rest -> f x ^ s ^ term s f rest

let comma_sep f xs = sep "," f xs

let semi_sep f xs = sep ";" f xs

let semi_term f xs = term ";" f xs

let max_prec = 10

let ty_prec t =
  match t with
  | TVar _ -> 0
  | QVar _ -> 0
  | TBool -> 0
  | TInt _ -> 0
  | TArrow _ -> 8
  | TTuple _ -> 6
  | TOption _ -> 4
  | TMap _ -> 4

let rec ty_to_string_p prec t =
  let p = ty_prec t in
  let s =
    match t with
    | TVar {contents= tv} -> tyvar_to_string tv
    | QVar name -> "{" ^ Var.to_string name ^ "}"
    | TBool -> "bool"
    | TInt i -> "int" ^ UInt32.to_string i
    | TArrow (t1, t2) -> ty_to_string_p p t1 ^ " -> " ^ ty_to_string_p prec t2
    | TTuple ts -> sep "*" (ty_to_string_p p) ts
    | TOption t -> "option[" ^ ty_to_string_p p t ^ "]"
    | TMap (t1, t2) ->
        "dict[" ^ ty_to_string_p p t1 ^ "," ^ ty_to_string_p p t2 ^ "]"
  in
  if p < prec then s else "(" ^ s ^ ")"

and tyvar_to_string tv =
  match tv with
  | Unbound (name, l) -> Var.to_string name ^ "[" ^ string_of_int l ^ "]"
  | Link ty -> "<" ^ ty_to_string_p max_prec ty ^ ">"

let ty_to_string t = ty_to_string_p max_prec t

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
  | MCreate -> "createMap"
  | MGet -> "at"
  | MSet -> "set"
  | MMap -> "map"
  | MMerge -> "combine"
  | MFilter -> "filter"

let rec pattern_to_string pattern =
  match pattern with
  | PWild -> "_"
  | PVar x -> Var.to_string x
  | PBool true -> "true"
  | PBool false -> "false"
  | PUInt32 i -> UInt32.to_string i
  | PTuple ps -> "(" ^ comma_sep pattern_to_string ps ^ ")"
  | POption None -> "None"
  | POption (Some p) -> "Some " ^ pattern_to_string p

let ty_env_to_string env = Env.to_string ty_to_string env.ty

let rec value_env_to_string env =
  Env.to_string (value_to_string_p max_prec) env.value

and env_to_string env =
  "[" ^ ty_env_to_string env ^ "|" ^ value_env_to_string env ^ "] "

and func_to_string_p prec {arg= x; argty= argt; resty= rest; body} =
  let s_arg =
    match argt with
    | None -> Var.to_string x
    | Some t -> "(" ^ Var.to_string x ^ ":" ^ ty_to_string t ^ ")"
  in
  let s_res =
    match rest with None -> "" | Some t -> " : " ^ ty_to_string t
  in
  let s = "fun " ^ s_arg ^ s_res ^ " -> " ^ exp_to_string_p max_prec body in
  if prec < max_prec then "(" ^ s ^ ")" else s

and closure_to_string_p prec (env, {arg= x; argty= argt; resty= rest; body}) =
  let s_arg =
    match argt with
    | None -> Var.to_string x
    | Some t -> "(" ^ Var.to_string x ^ ":" ^ ty_to_string t ^ ")"
  in
  let s_res =
    match rest with None -> "" | Some t -> " : " ^ ty_to_string t
  in
  let s =
    "fun" ^ env_to_string env ^ s_arg ^ s_res ^ " -> "
    ^ exp_to_string_p prec body
  in
  if prec < max_prec then "(" ^ s ^ ")" else s

and map_to_string sep_s term_s m =
  let binding_to_string (k, v) =
    value_to_string_p max_prec k ^ sep_s ^ value_to_string_p max_prec v
  in
  let bs, default = IMap.bindings m in
  "["
  ^ term term_s binding_to_string bs
  ^ "default:="
  ^ value_to_string_p max_prec default
  ^ "]"

and value_to_string_p prec v =
  match v.v with
  | VBool true -> "true"
  | VBool false -> "false"
  | VUInt32 i -> UInt32.to_string i
  | VMap m -> map_to_string ":=" "," m
  | VTuple vs -> "(" ^ comma_sep (value_to_string_p max_prec) vs ^ ")"
  | VOption None -> "None"
  | VOption (Some v) ->
      let s = "Some(" ^ value_to_string_p max_prec v ^ ")" in
      if max_prec > prec then "(" ^ s ^ ")" else s
  | VClosure cl -> closure_to_string_p prec cl

and exp_to_string_p prec e =
  let p = prec_exp e in
  let s =
    match e.e with
    | EVar x -> Var.to_string x
    | EVal v -> value_to_string_p prec v
    | EOp (op, es) -> op_args_to_string prec p op es
    | EFun f -> func_to_string_p prec f
    | EApp (e1, e2) ->
        exp_to_string_p prec e1 ^ " " ^ exp_to_string_p p e2 ^ " "
    | EIf (e1, e2, e3) ->
        "if "
        ^ exp_to_string_p max_prec e1
        ^ " then "
        ^ exp_to_string_p max_prec e2
        ^ " else " ^ exp_to_string_p prec e3
    | ELet (x, e1, e2) ->
        "let " ^ Var.to_string x ^ "="
        ^ exp_to_string_p max_prec e1
        ^ " in " ^ exp_to_string_p prec e2
    | ETuple es -> "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
    | ESome e -> "Some(" ^ exp_to_string_p prec e ^ ")"
    | EMatch (e1, bs) ->
        "(match "
        ^ exp_to_string_p max_prec e1
        ^ " with " ^ branches_to_string prec bs ^ ")"
    | ETy (e, t) -> exp_to_string_p prec e ^ ty_to_string t
  in
  if p > prec then "(" ^ s ^ ")" else s

and branch_to_string prec (p, e) =
  " | " ^ pattern_to_string p ^ " -> " ^ exp_to_string_p prec e

and branches_to_string prec bs =
  match bs with
  | [] -> ""
  | b :: bs -> branch_to_string prec b ^ branches_to_string prec bs

and op_args_to_string prec p op es =
  if is_keyword_op op then
    op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
  else
    match es with
    | [] -> op_to_string op ^ "()" (* should not happen *)
    | [e1] -> op_to_string op ^ exp_to_string_p p e1
    | [e1; e2] ->
        exp_to_string_p p e1 ^ " " ^ op_to_string op ^ " "
        ^ exp_to_string_p prec e2
    | es ->
        op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"

let value_to_string v = value_to_string_p max_prec v

let exp_to_string e = exp_to_string_p max_prec e

let func_to_string f = func_to_string_p max_prec f

let closure_to_string c = closure_to_string_p max_prec c

let rec declaration_to_string d =
  match d with
  | DLet (x, tyo, e) ->
      let ty_str =
        match tyo with None -> "" | Some ty -> ":" ^ ty_to_string ty ^ " "
      in
      "let " ^ Var.to_string x ^ ty_str ^ " = " ^ exp_to_string e
  | DSymbolic (x, Exp e) ->
      "symbolic " ^ Var.to_string x ^ " = " ^ exp_to_string e
  | DSymbolic (x, Ty ty) ->
      "symbolic " ^ Var.to_string x ^ " : " ^ ty_to_string ty
  | DMerge e -> "let merge = " ^ exp_to_string e
  | DTrans e -> "let trans = " ^ exp_to_string e
  | DAssert e -> "let assert = " ^ exp_to_string e
  | DRequire e -> "require " ^ exp_to_string e
  | DNodes n -> "let nodes = " ^ UInt32.to_string n
  | DEdges es ->
      "let edges = {"
      ^ List.fold_right
          (fun (u, v) s -> UInt32.to_string u ^ "=" ^ UInt32.to_string v ^ ";")
          es ""
      ^ "}"
  | DInit e -> "let init = " ^ exp_to_string e
  | DATy t -> "type attribute = " ^ ty_to_string t

let rec declarations_to_string ds =
  match ds with
  | [] -> ""
  | d :: ds -> declaration_to_string d ^ "\n" ^ declarations_to_string ds
