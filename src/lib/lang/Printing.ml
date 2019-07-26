(* Printing utilities for abstract syntax *)

open Syntax
open Nv_datatypes
open Nv_utils.PrimitiveCollections
open Nv_utils.RecordUtils

let is_keyword_op op =
  match op with
  | And | Or | Not | UAdd _ | USub _ | Eq | ULess _ | ULeq _ | MGet | NLess | NLeq -> false
  | TGet _| TSet _| MCreate | MSet | MMap | MMerge | MFoldNode | MFoldEdge | MMapFilter | AtMost _ -> true

(* set to true if you want to print universal quanifiers explicitly *)
let quantifiers = true

let max_prec = 10

let prec_op op =
  match op with
  | And -> 7
  | Or -> 7
  | Not -> 6
  | UAdd _ -> 4
  | USub _ -> 4
  | Eq -> 5
  | ULess _ -> 5
  | ULeq _ -> 5
  | NLess -> 5
  | NLeq -> 5
  | TGet _ -> 5
  | TSet _ -> 5
  | MCreate -> 5
  | MGet -> 5
  | MSet -> 3
  | MMap -> 5
  | MMerge -> 5
  | MFoldNode -> 5
  | MFoldEdge -> 5
  | MMapFilter -> 5
  | AtMost _ -> 6


let prec_exp e =
  let open Syntax in
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
  let open Syntax in
  match t with
  | TUnit -> 0
  | TVar _ -> 0
  | QVar _ -> 0
  | TBool -> 0
  | TInt _ -> 0
  | TNode -> 0
  | TEdge -> 0
  | TArrow _ -> 8
  | TTuple _ -> 6
  | TOption _ -> 4
  | TMap _ -> 4
  | TRecord _ -> 6

let list_to_string f lst =
  "[ " ^
  List.fold_left (fun s1 elt -> s1 ^ f elt ^ "; ") "" lst ^
  "] "
;;

let rec ty_to_string_p prec t =
  let p = ty_prec t in
  let s =
    match t with
    | TVar {contents= tv} -> tyvar_to_string tv
    | QVar name -> "{" ^ Var.to_string name ^ "}"
    | TUnit -> "unit"
    | TBool -> "bool"
    | TInt i -> "int" ^ string_of_int i
    | TNode -> "node"
    | TEdge -> "edge"
    | TArrow (t1, t2) ->
      ty_to_string_p p t1 ^ " -> " ^ ty_to_string_p prec t2
    | TTuple ts -> "(" ^ sep "*" (ty_to_string_p p) ts ^ ")"
    | TOption t -> "option[" ^ ty_to_string_p p t ^ "]"
    | TMap (t1, t2) ->
      "dict[" ^ ty_to_string_p p t1 ^ "," ^ ty_to_string_p p t2
      ^ "]"
    | TRecord map -> print_record ":" (ty_to_string_p prec) map

  in
  if p < prec then s else "(" ^ s ^ ")"

and tyvar_to_string tv =
  match tv with
  | Unbound (name, l) ->
    Var.to_string name ^ "[" ^ string_of_int l ^ "]"
  | Link ty -> "<" ^ ty_to_string_p max_prec ty ^ ">"

let ty_to_string t = ty_to_string_p max_prec t

let op_to_string op =
  let open Syntax in
  match op with
  | And -> "&&"
  | Or -> "||"
  | Not -> "!"
  | UAdd n -> "+" ^ "u" ^ (string_of_int n)
  | USub n -> "-" ^ "u" ^ (string_of_int n)
  | Eq -> "="
  | ULess n -> "<" ^ "u" ^ (string_of_int n)
  | ULeq n -> "<=" ^ "u" ^ (string_of_int n)
  | NLess -> "<n"
  | NLeq -> "<=n"
  | TGet (n1, n2, n3) -> Printf.sprintf "tuple%dGet%d-%d" n1 n2 n3
  | TSet (n1, n2, n3) -> Printf.sprintf "tuple%dSet%d-%d" n1 n2 n3
  | MCreate -> "createMap"
  | MGet -> "at"
  | MSet -> "set"
  | MMap -> "map"
  | MMapFilter -> "mapIf"
  | MMerge -> "combine"
  | MFoldNode -> "foldNodes"
  | MFoldEdge -> "foldEdges"
  | AtMost _ -> "atMost"

let rec pattern_to_string pattern =
  let open Syntax in
  match pattern with
  | PWild -> "_"
  | PVar x -> Var.to_string x
  | PUnit -> "()"
  | PBool true -> "true"
  | PBool false -> "false"
  | PInt i -> Integer.to_string i
  | PTuple ps -> "(" ^ comma_sep pattern_to_string ps ^ ")"
  | POption None -> "None"
  | POption (Some p) -> "Some " ^ pattern_to_string p
  | PRecord map -> print_record "=" pattern_to_string map
  | PNode n -> Printf.sprintf "%dn" n
  | PEdge (p1, p2) -> Printf.sprintf "%s~%s" (pattern_to_string p1) (pattern_to_string p2)

let ty_env_to_string env = Nv_datastructures.Env.to_string ty_to_string env.ty

let glob = ref false
let rec value_env_to_string env =
  Nv_datastructures.Env.to_string (value_to_string_p max_prec) env.value

and env_to_string env =
  let open Nv_datastructures in
  if env.ty = Env.empty && env.value = Env.empty then " "
  else
    "[" ^ ty_env_to_string env ^ "|" ^ value_env_to_string env ^ "] "

and func_to_string_p prec {arg= x; argty= argt; resty= rest; body} =
  let s_arg = Var.to_string x in
  let s = "fun " ^ s_arg ^ " -> " ^ exp_to_string_p max_prec body in
  if prec < max_prec then "(" ^ s ^ ")" else s

and closure_to_string_p prec
    (env, {arg= x; argty= argt; resty= rest; body}) =
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
    value_to_string_p max_prec k
    ^ sep_s
    ^ value_to_string_p max_prec v
  in
  let bs, default = BddMap.bindings m in
  "["
  ^ term term_s binding_to_string bs
  ^ "default:="
  ^ value_to_string_p max_prec default
  ^ "]"

and value_to_string_p prec v =
  match v.v with
  | VUnit -> "()"
  | VBool true -> "true"
  | VBool false -> "false"
  | VInt i -> Integer.to_string i
  | VMap m -> map_to_string ":=" "," m
  | VTuple vs ->
    "(" ^ comma_sep (value_to_string_p max_prec) vs ^ ")"
  | VOption None -> (* Printf.sprintf "None:%s" (ty_to_string (oget v.vty)) *)
    "None"
  | VOption (Some v) ->
    let s = "Some(" ^ value_to_string_p max_prec v ^ ")" in
    if max_prec > prec then "(" ^ s ^ ")" else s
  | VClosure cl -> closure_to_string_p prec cl
  | VRecord map -> print_record "=" (value_to_string_p prec) map
  | VNode n -> Printf.sprintf "%dn" n
  | VEdge (n1, n2) -> Printf.sprintf "%dn-%dn" n1 n2

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
      ^ " then \n"
      ^ exp_to_string_p max_prec e2
      ^ " else \n" ^ exp_to_string_p prec e3
    | ELet (x, e1, e2) ->
      "let " ^ Var.to_string x ^ "="
      ^ exp_to_string_p max_prec e1
      ^ " in \n" ^ exp_to_string_p prec e2
    | ETuple es ->
      "(" ^ comma_sep (exp_to_string_p max_prec) es ^ ")"
    | ESome e -> "Some(" ^ exp_to_string_p prec e ^ ")"
    | EMatch (e1, bs) ->
      "(match "
      ^ exp_to_string_p max_prec e1
      ^ " with " ^ "\n"
      ^ branches_to_string prec (branchToList bs)
      ^ ")"
    | ETy (e, t) -> exp_to_string_p prec e ^ ty_to_string t
    | ERecord map -> print_record "=" (exp_to_string_p prec) map
    | EProject (e, l) -> exp_to_string_p prec e ^ "." ^ l
  in
  if p > prec then "(" ^ s ^ ")" else s

and branch_to_string prec (p, e) =
  " | " ^ pattern_to_string p ^ " -> " ^ exp_to_string_p prec e

and branches_to_string prec bs =
  match bs with
  | [] -> ""
  | b :: bs -> branch_to_string prec b ^ "\n" ^ branches_to_string prec bs

and op_args_to_string prec p op es =
  if is_keyword_op op then
    op_to_string op ^ "("
    ^ comma_sep (exp_to_string_p max_prec) es
    ^ ")"
  else
    match es with
    | [] -> op_to_string op ^ "()" (* should not happen *)
    | [e1] -> op_to_string op ^ exp_to_string_p p e1
    | [e1; e2] ->
      exp_to_string_p p e1 ^ " " ^ op_to_string op ^ " "
      ^ exp_to_string_p prec e2
    | es ->
      op_to_string op ^ "("
      ^ comma_sep (exp_to_string_p max_prec) es
      ^ ")"

let value_to_string v = value_to_string_p max_prec v

let exp_to_string e = exp_to_string_p max_prec e

let func_to_string f = func_to_string_p max_prec f

let closure_to_string c = closure_to_string_p max_prec c

(* TODO: should the let statements use the identifiers defined in Syntax instead? *)
let rec declaration_to_string d =
  match d with
  | DLet (x, tyo, e) ->
    let ty_str =
      match tyo with
      | None -> ""
      | Some ty -> ":" ^ ty_to_string ty ^ " "
    in
    "let " ^ Var.to_string x ^ ty_str ^ " = " ^ exp_to_string e
  | DSymbolic (x, Exp e) ->
    "symbolic " ^ Var.to_string x ^ " = " ^ exp_to_string e
  | DSymbolic (x, Ty ty) ->
    "symbolic " ^ Var.to_string x ^ " : " ^ ty_to_string ty
  | DMerge e -> "let merge = " ^ exp_to_string e
  | DTrans e -> "let trans = " ^ exp_to_string e
  | DAssert e -> "let assert = " ^ exp_to_string e
  | DPartition e -> "let partition = " ^ exp_to_string e (* partitioning *)
  | DInterface e -> "let interface = " ^ exp_to_string e (* partitioning *)
  | DRequire e -> "require " ^ exp_to_string e
  | DNodes n -> "let nodes = " ^ string_of_int n
  | DEdges es ->
    "let edges = {"
    ^ List.fold_right
      (fun (u, v) s ->
         Printf.sprintf "%s%dn-%dn;" s u v
      )
      es ""
    ^ "}"
  | DInit e -> "let init = " ^ exp_to_string e
  | DATy t -> "type attribute = " ^ ty_to_string t
  | DUserTy (name, ty) ->
    Printf.sprintf "type %s = %s" (Var.to_string name) (ty_to_string ty)

let rec declarations_to_string ds =
  match ds with
  | [] -> ""
  | d :: ds ->
    declaration_to_string d ^ "\n" ^ declarations_to_string ds

let network_to_string ?(show_topology=false) (net : Syntax.network) =
  BatString.concat "" @@

  (** User types **)
  List.mapi (fun i map ->
      Printf.sprintf "type record_%d = %s\n" i (print_record ":" ty_to_string map))
    net.utys
  @ ["\n"] @
  (** Attr type **)
  [ Printf.sprintf "type attribute = %s\n" (ty_to_string net.attr_type) ]
  @ ["\n"] @
  (** Topology -- hide unless specifically requested **)
  (if not show_topology then [] else
    let open Nv_datastructures in
     [
       Printf.sprintf "let nodes = %d\n\n" (AdjGraph.num_vertices net.graph);

       Printf.sprintf "let edges = {%s}\n\n" @@ list_to_string
         (fun (i, j) -> Printf.sprintf "%dn-%dn" i j)
         (AdjGraph.edges net.graph);
     ])
  @
  (** Symbolic Variables **)
  List.map (fun (var, toe) ->
      Printf.sprintf "symbolic %s %s\n" (Var.to_string var) @@
      match toe with
      | Ty ty -> ": " ^ ty_to_string ty
      | Exp e -> "= " ^ exp_to_string e)
    net.symbolics
  @ ["\n"] @
  (** Requires **)
  List.map (fun e -> Printf.sprintf "require %s\n" (exp_to_string e)) net.requires
  @ ["\n"] @
  (** Additional declarations **)
  List.map
    (fun (var, tyo, e) ->
       Printf.sprintf "let %s%s = %s\n\n"
         (Var.to_string var)
         (match tyo with None -> "" | Some ty -> " : " ^ ty_to_string ty)
         (exp_to_string e))
    net.defs
  @
  [
    Printf.sprintf "let init = %s\n\n" @@ exp_to_string net.init;
    Printf.sprintf "let trans = %s\n\n" @@ exp_to_string net.trans;
    Printf.sprintf "let merge = %s\n\n" @@ exp_to_string net.merge;
  ]
  @
  (match net.assertion with
   | None -> []
   | Some e -> [Printf.sprintf "let assert = %s\n\n" @@ exp_to_string e]
  )
  (* partitioning *)
  @
  (match net.partition with
   | None -> []
   | Some e -> [Printf.sprintf "let partition = %s\n\n" @@ exp_to_string e]
  )
  @
  (match net.interface with
   | None -> []
   | Some e -> [Printf.sprintf "let interface = %s\n\n" @@ exp_to_string e]
  )
 (* end partitioning *)
