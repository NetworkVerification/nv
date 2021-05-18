(* Printing utilities for abstract syntax *)
open Batteries
open Syntax
open Nv_datastructures
open Nv_utils.PrimitiveCollections
open Nv_utils.RecordUtils
open Nv_utils

type op_position =
  | Prefix of string
  | Infix of string
  | Circumfix of string list

(** Precedence levels determine where parentheses are used to distinguish expressions.
 ** A higher precedence expression enclosed by a lower precedence expression has parentheses.
 ** The topmost level always starts at maximum precedence. *)
let max_prec = 10

let prec_op op =
  match op with
  | And -> 7
  | Or -> 7
  | Not -> 4
  | UAdd _ -> 4
  | USub _ -> 4
  | Eq -> 5
  | ULess _ -> 5
  | ULeq _ -> 5
  | UAnd _ -> 5
  | NLess -> 5
  | NLeq -> 5
  | TGet _ -> 5
  | TSet _ -> 5
  | MCreate -> 5
  | MGet -> 5
  | MSet -> 3
  | MMap -> 5
  | MMerge -> 5
  | MForAll -> 5
  | MFoldNode -> 5
  | MFoldEdge -> 5
  | MMapFilter -> 5
  | MMapIte -> 5
  | AtMost _ -> 6
;;

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
  | ERecord _ -> 0
  | EProject _ -> 0
;;

let rec sep s f xs =
  match xs with
  | [] -> ""
  | [x] -> f x
  | x :: y :: rest -> f x ^ s ^ sep s f (y :: rest)
;;

let rec term s f xs =
  match xs with
  | [] -> ""
  | _ -> PrimitiveCollections.printList f xs "" s ""
;;

let space_sep f xs = sep " " f xs
let comma_sep f xs = sep "," f xs
let semi_sep f xs = sep ";" f xs
let semi_term f xs = term ";" f xs
let list_to_string f lst = PrimitiveCollections.printList f lst "[" ";" "]"

(* The way we print our types means that we don't really need precedence rules.
   The only type which isn't totally self-contained is TArrow *)
let rec ty_to_string t =
  match t with
  | TVar { contents = tv } -> tyvar_to_string tv
  | QVar name -> "{" ^ Var.to_string name ^ "}"
  | TUnit -> "unit"
  | TBool -> "bool"
  | TInt i -> "int" ^ string_of_int i
  | TNode -> "tnode"
  | TEdge -> "tedge"
  | TTuple ts ->
    if List.is_empty ts
    then "TTuple0"
    else if List.length ts = 1
    then "TTuple1(" ^ ty_to_string (List.hd ts) ^ ")"
    else "(" ^ sep "," ty_to_string ts ^ ")"
  | TOption t -> "option[" ^ ty_to_string t ^ "]"
  | TMap (t1, t2) -> "dict[" ^ ty_to_string t1 ^ "," ^ ty_to_string t2 ^ "]"
  | TRecord map -> print_record ":" ty_to_string map
  | TArrow (t1, t2) ->
    let leftside =
      match t1 with
      | TArrow _ -> "(" ^ ty_to_string t1 ^ ")"
      | _ -> ty_to_string t1
    in
    leftside ^ " -> " ^ ty_to_string t2

and tyvar_to_string tv =
  match tv with
  | Unbound (name, l) -> Var.to_string name ^ "[" ^ string_of_int l ^ "]"
  | Link ty -> "<" ^ ty_to_string ty ^ ">"
;;

let op_pos_to_string op =
  match op with
  | And -> Infix "&&"
  | Or -> Infix "||"
  | Not -> Prefix "!"
  | UAdd n -> Infix ("+" ^ "u" ^ string_of_int n)
  | USub n -> Infix ("-" ^ "u" ^ string_of_int n)
  | UAnd n -> Infix ("&" ^ "u" ^ string_of_int n)
  | Eq -> Infix "="
  | ULess n -> Infix ("<" ^ "u" ^ string_of_int n)
  | ULeq n -> Infix ("<=" ^ "u" ^ string_of_int n)
  | NLess -> Infix "<n"
  | NLeq -> Infix "<=n"
  | TGet (n1, n2, n3) -> Prefix (Printf.sprintf "tuple%dGet%d-%d" n1 n2 n3)
  | TSet (n1, n2, n3) -> Prefix (Printf.sprintf "tuple%dSet%d-%d" n1 n2 n3)
  | MCreate -> Prefix "createDict"
  | MGet -> Circumfix ["["; "]"]
  | MSet -> Circumfix ["["; ":="; "]"]
  | MMap -> Prefix "map"
  | MMapFilter -> Prefix "mapIf"
  | MMapIte -> Prefix "mapIte"
  | MMerge -> Prefix "combine"
  | MFoldNode -> Prefix "foldNodes"
  | MFoldEdge -> Prefix "foldEdges"
  | AtMost _ -> Prefix "atMost"
  | MForAll -> Prefix "forAll"
;;

let op_to_string op =
  match op_pos_to_string op with
  | Prefix s | Infix s -> s
  | Circumfix ss ->
    (* create a set of dummy variables from 'a' onwards *)
    let dummies = List.init (List.length ss) (fun n -> Char.chr (n + 61)) in
    List.fold_left2 (fun s d o -> s ^ Char.escaped d ^ o) "" dummies ss
;;

let rec pattern_to_string pattern =
  match pattern with
  | PWild -> "_"
  | PVar x -> Var.to_string x
  | PUnit -> "PUnit"
  | PBool true -> "true"
  | PBool false -> "false"
  | PInt i -> Integer.to_string i
  | PTuple ps ->
    if List.is_empty ps
    then "PTuple0"
    else if List.length ps = 1
    then "PTuple1(" ^ pattern_to_string (List.hd ps) ^ ")"
    else "(" ^ comma_sep pattern_to_string ps ^ ")"
  | POption None -> "None"
  | POption (Some p) -> "Some " ^ pattern_to_string p
  | PRecord map -> print_record "=" pattern_to_string map
  | PNode n -> Printf.sprintf "%dn" n
  | PEdge (p1, p2) -> Printf.sprintf "%s~%s" (pattern_to_string p1) (pattern_to_string p2)
;;

let padding i = String.init i (fun _ -> ' ')
let ty_env_to_string env = Env.to_string ty_to_string env.ty

let tyo_to_string tyo =
  match tyo with
  | None -> "None"
  | Some ty -> ty_to_string ty
;;

let glob = ref false

let rec value_env_to_string ~show_types env =
  Env.to_string (value_to_string_p ~show_types max_prec) env.value

and env_to_string ?(show_types = false) env =
  if env.ty = Env.empty && env.value = Env.empty
  then " "
  else "[" ^ ty_env_to_string env ^ "|" ^ value_env_to_string ~show_types env ^ "] "

and func_to_string_p ~show_types prec { arg = x; argty; resty = _; body } =
  let s_arg = Var.to_string x in
  let arg_str =
    if show_types then Printf.sprintf "(%s : %s)" s_arg (tyo_to_string argty) else s_arg
  in
  let s =
    Printf.sprintf "fun %s -> %s " arg_str (exp_to_string_p ~show_types max_prec body)
  in
  if prec < max_prec then "(" ^ s ^ ")" else s

and closure_to_string_p
    ~show_types
    prec
    (env, { arg = x; argty = argt; resty = rest; body })
  =
  let s_arg =
    match argt with
    | None -> Var.to_string x
    | Some t -> "(" ^ Var.to_string x ^ ":" ^ ty_to_string t ^ ")"
  in
  let s_res =
    match rest with
    | None -> ""
    | Some t -> " : " ^ ty_to_string t
  in
  let s =
    "fun"
    ^ env_to_string ~show_types env
    ^ s_arg
    ^ s_res
    ^ " -> "
    ^ exp_to_string_p ~show_types prec body
  in
  if prec < max_prec then "(" ^ s ^ ")" else s

and map_to_string ~show_types sep_s term_s m =
  let binding_to_string (k, v) =
    (* BddMap.multiValue_to_string k *)
    value_to_string_p ~show_types max_prec k
    ^ sep_s
    ^ value_to_string_p ~show_types max_prec v
  in
  let bs, dv = BddMap.bindings m in
  let dv_string = value_to_string_p ~show_types max_prec dv in
  match bs with
  | [] -> Printf.sprintf "{ _ |-> %s }" dv_string
  | _ -> Printf.sprintf "{ %s ; _ |-> %s}" (term term_s binding_to_string bs) dv_string

and value_to_string_p ~show_types prec v =
  let value_to_string_p = value_to_string_p ~show_types in
  match v.v with
  | VUnit -> "VUnit"
  | VBool true -> "true"
  | VBool false -> "false"
  | VInt i -> Integer.to_string i
  | VMap m -> map_to_string ~show_types " |-> " "; " m
  | VTuple vs ->
    if List.is_empty vs
    then "VTuple0"
    else if List.length vs = 1
    then "VTuple1(" ^ value_to_string_p max_prec (List.hd vs) ^ ")"
    else "(" ^ comma_sep (value_to_string_p max_prec) vs ^ ")"
  | VOption None ->
    (* Printf.sprintf "None:%s" (ty_to_string (oget v.vty)) *)
    "None"
  | VOption (Some v) ->
    let s = "Some " ^ value_to_string_p max_prec v in
    if max_prec > prec then "(" ^ s ^ ")" else s
  | VClosure cl -> closure_to_string_p ~show_types prec cl
  | VRecord map -> print_record "=" (value_to_string_p prec) map
  | VNode n -> Printf.sprintf "%dn" n
  | VEdge (n1, n2) -> Printf.sprintf "%d~%d" n1 n2

and exp_to_string_p ~show_types prec e =
  let exp_to_string_p = exp_to_string_p ~show_types in
  let value_to_string_p = value_to_string_p ~show_types in
  let p = prec_exp e in
  let s =
    match e.e with
    | EVar x -> Var.to_string x
    | EVal v -> value_to_string_p prec v
    | EOp (op, es) -> op_args_to_string ~show_types prec p op es
    | EFun f -> func_to_string_p ~show_types p f
    | EApp (e1, e2) -> exp_to_string_p prec e1 ^ " " ^ exp_to_string_p p e2 ^ " "
    | EIf (e1, e2, e3) ->
      "if "
      ^ exp_to_string_p max_prec e1
      ^ " then \n"
      ^ exp_to_string_p max_prec e2
      ^ " else \n"
      ^ exp_to_string_p prec e3
    | ELet (x, e1, e2) ->
      "let "
      ^ Var.to_string x
      ^ "="
      ^ exp_to_string_p max_prec e1
      ^ " in \n"
      ^ exp_to_string_p prec e2
    | ETuple es ->
      if List.is_empty es
      then "ETuple0"
      else if List.length es = 1
      then "ETuple1(" ^ exp_to_string_p max_prec (List.hd es) ^ ")"
      else "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
    | ESome e -> "Some " ^ exp_to_string_p prec e
    | EMatch (e1, bs) ->
      "(match "
      ^ exp_to_string_p max_prec e1
      ^ " with "
      ^ "\n"
      ^ branches_to_string ~show_types prec (branchToList bs)
      ^ ")"
    | ETy (e, t) -> exp_to_string_p prec e ^ ty_to_string t
    | ERecord map -> print_record "=" (exp_to_string_p prec) map
    | EProject (e, l) -> exp_to_string_p prec e ^ "." ^ l
  in
  if show_types
  then Printf.sprintf "(%s : %s)" s (tyo_to_string e.ety)
  else if p > prec
  then "(" ^ s ^ ")"
  else s

and branch_to_string ~show_types prec (p, e) =
  " | " ^ pattern_to_string p ^ " -> " ^ exp_to_string_p ~show_types prec e

and branches_to_string ~show_types prec bs =
  match bs with
  | [] -> ""
  | b :: bs ->
    branch_to_string ~show_types prec b ^ "\n" ^ branches_to_string ~show_types prec bs

(* prec is the precedence of the outer expression, while p is the precedence of the eop *)
and op_args_to_string ~show_types prec p op es =
  let exp_to_string_p = exp_to_string_p ~show_types in
  match op_pos_to_string op with
  | Prefix o ->
    (match es with
    | [e1] -> o ^ " " ^ exp_to_string_p p e1
    | es -> o ^ " " ^ space_sep (exp_to_string_p p) es)
  | Infix o ->
    (match es with
    | [e1; e2] -> exp_to_string_p p e1 ^ " " ^ o ^ " " ^ exp_to_string_p prec e2
    | es -> sep (" " ^ o ^ " ") (exp_to_string_p p) es)
  | Circumfix os ->
    (* need to make sure that os has same length as es *)
    List.fold_left2 (fun s e o -> s ^ exp_to_string_p p e ^ o) "" es os
;;

(* if is_keyword_op op
 * then op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
 * else (
 *   match es with
 *   | [] -> op_to_string op ^ "()" (\* should not happen *\)
 *   | [e1] -> op_to_string op ^ exp_to_string_p p e1
 *   | [e1; e2] ->
 *     exp_to_string_p p e1 ^ " " ^ op_to_string op ^ " " ^ exp_to_string_p prec e2
 *   | es -> op_to_string op ^ "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")") *)

let value_to_string ?(show_types = false) v = value_to_string_p ~show_types max_prec v
let exp_to_string ?(show_types = false) e = exp_to_string_p ~show_types max_prec e
let func_to_string ?(show_types = false) f = func_to_string_p ~show_types max_prec f
let closure_to_string ?(show_types = false) c = closure_to_string_p ~show_types max_prec c

let part_to_string ?(show_types = false) { interface; decomp = lt, rt } =
  let exp_to_string = exp_to_string ~show_types in
  let oprint s o =
    match o with
    | None -> ""
    | Some e -> Printf.sprintf "; %s = %s" s (exp_to_string e)
  in
  Printf.sprintf
    "; interface = %s%s%s"
    (exp_to_string interface)
    (oprint "ltrans" lt)
    (oprint "rtrans" rt)
;;

(* TODO: should the let statements use the identifiers defined in Syntax instead? *)
let rec declaration_to_string ?(show_types = false) d =
  let exp_to_string = exp_to_string ~show_types in
  match d with
  | DLet (x, tyo, e) ->
    let ty_str =
      match tyo with
      | None -> ""
      | Some ty -> ":" ^ ty_to_string ty ^ " "
    in
    "let " ^ Var.to_string x ^ ty_str ^ " = " ^ exp_to_string e
  | DSymbolic (x, Exp e) -> "symbolic " ^ Var.to_string x ^ " = " ^ exp_to_string e
  | DSymbolic (x, Ty ty) -> "symbolic " ^ Var.to_string x ^ " : " ^ ty_to_string ty
  | DAssert e -> "assert " ^ exp_to_string e
  | DSolve { aty; var_names; init; trans; merge; part } ->
    Printf.sprintf
      "let %s = solution<%s> {init = %s; trans = %s; merge = %s%s}"
      (exp_to_string var_names)
      (match aty with
      | None -> "None"
      | Some ty -> ty_to_string ty)
      (exp_to_string init)
      (exp_to_string trans)
      (exp_to_string merge)
      (match part with
      | None -> ""
      | Some p -> part_to_string p)
  | DPartition e -> "let partition = " ^ exp_to_string e (* partitioning *)
  | DRequire e -> "require " ^ exp_to_string e
  | DNodes n -> "let nodes = " ^ string_of_int n
  | DEdges es ->
    "let edges = {"
    ^ List.fold_right (fun (u, v) s -> Printf.sprintf "%s%dn-%dn;" s u v) es ""
    ^ "}"
  | DUserTy (name, ty) ->
    Printf.sprintf "type %s = %s" (Var.to_string name) (ty_to_string ty)
;;

let rec declarations_to_string ?(show_types = false) ds =
  match ds with
  | [] -> ""
  | d :: ds ->
    declaration_to_string ~show_types d ^ "\n" ^ declarations_to_string ~show_types ds
;;
