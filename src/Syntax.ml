(* Abstract syntax of SRP attribute processing expressions *)
open BatMap
open Unsigned

(* indices into maps or map sizes must be static constants *)
type index = UInt32.t

(* see:  http://okmij.org/ftp/ML/generalization.html *)
type level = int

type tyname = Var.t

type ty =
  | TVar of tyvar ref
  | QVar of tyname
  | TBool
  | TInt of index
  | TArrow of ty * ty
  | TTuple of ty list
  | TOption of ty
  | TMap of ty * ty

and tyvar = Unbound of tyname * level | Link of ty

type var = Var.t

type op =
  | And
  | Or
  | Not
  | UAdd
  | USub
  | UEq
  | ULess
  | ULeq
  | MCreate
  | MGet
  | MSet
  | MMap
  | MMerge
  | MFilter

type pattern =
  | PWild
  | PVar of var
  | PBool of bool
  | PUInt32 of UInt32.t
  | PTuple of pattern list
  | POption of pattern option

type v =
  | VBool of bool
  | VUInt32 of UInt32.t
  | VMap of (value, value) IMap.t
  | VTuple of value list
  | VOption of value option
  | VClosure of closure

and value = {v: v; vty: ty option; vspan: Span.t}

and e =
  | EVar of var
  | EVal of value
  | EOp of op * exp list
  | EFun of func
  | EApp of exp * exp
  | EIf of exp * exp * exp
  | ELet of var * exp * exp
  | ETuple of exp list
  | ESome of exp
  | EMatch of exp * branches
  | ETy of exp * ty

and exp = {e: e; ety: ty option; espan: Span.t}

and branches = (pattern * exp) list

and func = {arg: var; argty: ty option; resty: ty option; body: exp}

and closure = (env * func)

and env = {ty: ty Env.t; value: value Env.t}

and ty_or_exp = Ty of ty | Exp of exp

type declaration =
  | DLet of var * ty option * exp
  | DSymbolic of var * ty_or_exp
  | DATy of ty
  | DMerge of exp
  | DTrans of exp
  | DInit of exp
  | DAssert of exp
  | DRequire of exp
  | DNodes of UInt32.t
  | DEdges of (UInt32.t * UInt32.t) list

type declarations = declaration list

(* Utilities *)

let arity op =
  match op with
  | And -> 2
  | Or -> 2
  | Not -> 1
  | UAdd -> 2
  | USub -> 2
  | UEq -> 2
  | ULess -> 2
  | ULeq -> 2
  | MCreate -> 1
  | MGet -> 2
  | MSet -> 3
  | MMap -> 2
  | MMerge -> 3
  | MFilter -> 2

(* Useful constructors *)

let ( ~> ) ty ty = TArrow (ty, ty)

let tint = TInt (UInt32.of_int 32)

let exp (e: e) : exp = {e; ety= None; espan= Span.default}

let wrap exp e = {e; ety= exp.ety; espan= exp.espan}

let value (v: v) : value = {v; vty= None; vspan= Span.default}

let e_val (x: v) : exp = exp (EVal (value x))

let func x body = {arg= x; argty= None; resty= None; body}

let ty_func tyargs body = (tyargs, body)

let lam x body = exp (EFun (func x body))

let oget (x: 'a option) : 'a =
  match x with None -> Console.error "internal error (oget)" | Some y -> y

let rec lams params body =
  match params with
  | [] -> Console.error "lams: no parameters"
  | [p] -> lam p body
  | p :: params -> lam p (lams params body)

let rec apps f args : exp =
  match args with
  | [] -> Console.error "apps: no arguments"
  | [a] -> exp (EApp (f, a))
  | a :: args -> apps (exp (EApp (f, a))) args

let apply_closure cl (args: value list) =
  apps (e_val (VClosure cl)) (List.map (fun a -> exp (EVal a)) args)

let get_decl ds f =
  try
    let daty : declaration =
      List.find (fun d -> match f d with None -> false | Some _ -> true) ds
    in
    f daty
  with _ -> None

let get_attr_type ds =
  get_decl ds (fun d -> match d with DATy ty -> Some ty | _ -> None)

let get_merge ds =
  get_decl ds (fun d -> match d with DMerge e -> Some e | _ -> None)

let get_trans ds =
  get_decl ds (fun d -> match d with DTrans e -> Some e | _ -> None)

let get_init ds =
  get_decl ds (fun d -> match d with DInit e -> Some e | _ -> None)

let get_assert ds =
  get_decl ds (fun d -> match d with DAssert e -> Some e | _ -> None)

let get_edges ds =
  get_decl ds (fun d -> match d with DEdges es -> Some es | _ -> None)

let get_nodes ds =
  get_decl ds (fun d -> match d with DNodes i -> Some i | _ -> None)

let get_symbolics ds =
  List.fold_left
    (fun acc d -> match d with DSymbolic (x, e) -> (x, e) :: acc | _ -> acc)
    [] ds
  |> List.rev

let get_requires ds =
  List.fold_left
    (fun acc d -> match d with DRequire e -> e :: acc | _ -> acc)
    [] ds
  |> List.rev

let prec v =
  match v.v with
  | VBool _ -> 1
  | VUInt32 _ -> 2
  | VMap _ -> 3
  | VTuple _ -> 4
  | VOption _ -> 5
  | VClosure _ -> 6

let rec compare_values v1 v2 =
  match (v1.v, v2.v) with
  | VBool b1, VBool b2 -> Pervasives.compare b1 b2
  | VUInt32 i1, VUInt32 i2 -> UInt32.compare i1 i2
  | VMap m1, VMap m2 -> IMap.compare compare_values m1 m2
  | VTuple vs1, VTuple vs2 -> compare_lists vs1 vs2
  | VOption vo1, VOption vo2 -> (
    match (vo1, vo2) with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some x, Some y -> compare_values x y )
  | VClosure (e1, f1), VClosure (e2, f2) ->
      let {ty= ty1; value= value1} = e1 in
      let {ty= ty2; value= value2} = e2 in
      let cmp = Env.compare Pervasives.compare ty1 ty1 in
      if cmp <> 0 then cmp else Env.compare compare_values value1 value2
  | _, _ -> prec v1 - prec v2

and compare_lists vs1 vs2 =
  match (vs1, vs2) with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | v1 :: vs1, v2 :: vs2 ->
      let cmp = compare_values v1 v2 in
      if cmp <> 0 then cmp else compare_lists vs1 vs2

and compare_maps m1 m2 = PMap.compare compare_values m1 m2
