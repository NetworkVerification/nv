open Nv_datatypes
open Nv_datastructures
open Nv_lang.Collections
open SmtLang

(* Classic encodes the SRP as an SMT expression, Functional encodes
   the problem as an NV term which is then translated to SMT *)
type encoding_style = Classic | Functional

type smt_options =
  { mutable verbose        : bool;
    mutable optimize       : bool;
    mutable encoding       : encoding_style;
    mutable unboxing       : bool;
    mutable failures       : int option;
    mutable multiplicities : int StringMap.t
  }

let smt_config : smt_options =
  { verbose = false;
    optimize = true;
    encoding = Classic;
    unboxing = false;
    failures = None;
    multiplicities = StringMap.empty
  }

let get_requires_no_failures req =
  let open Nv_lang.Syntax in
  BatList.filter (fun e -> match e.e with
      | EOp (AtMost _, _) -> false
      | _ -> true) req

let get_requires_failures req =
  let open Nv_lang.Syntax in
  BatList.filter (fun e -> match e.e with
      | EOp (AtMost _, _) -> true
      | _ -> false) req
  |> List.hd


module Constant =
struct
  type t = constant

  let compare x y = compare x.cname y.cname
end

module ConstantSet = BatSet.Make(Constant)

type smt_env =
  { mutable ctx: command list
  ; mutable const_decls: ConstantSet.t (** named constant and its sort *)
  ; mutable type_decls: datatype_decl StringMap.t
  ; mutable symbolics: Nv_lang.Syntax.ty_or_exp VarMap.t }

let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n =
  if descr = "" then Var.to_string n
  else Printf.sprintf "%s-%s" descr (Var.to_string n)

(** * Returns the SMT name of a datatype *)
let rec datatype_name (ty : Nv_lang.Syntax.ty) : string option =
  let open Nv_lang.Syntax in
  match ty with
  | TVar {contents= Link t} -> datatype_name t
  | TTuple ts -> (
      match ts with
      | [t] -> datatype_name t
      | ts ->
        let len = BatList.length ts in
        Some (Printf.sprintf "Pair%d" len))
  | TOption _ty -> Some "Option"
  | _ -> None

let add_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  env.const_decls <- ConstantSet.add {cname; csort; cdescr; cloc} env.const_decls

let mk_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  add_constant env ~cdescr:cdescr ~cloc:cloc cname csort;
  (mk_var cname) |> (mk_term ~tdescr:cdescr ~tloc:cloc)

let add_constraint (env : smt_env) (c : term) =
  env.ctx <- (mk_assert c |> mk_command) :: env.ctx

let is_symbolic syms x =
  VarMap.mem x syms

let is_var (tm: SmtLang.term) =
  match tm.t with
  | Var _ -> true
  | _ -> false

let rec ty_to_sort (ty: Nv_lang.Syntax.ty) : sort =
  let open Nv_lang.Syntax in
  match ty with
  | TVar {contents= Link t} -> ty_to_sort t
  | TUnit -> UnitSort
  | TBool -> BoolSort
  | TInt _ -> IntSort
  | TNode -> ty_to_sort (TInt 32)
  | TEdge -> ty_to_sort (TTuple [TNode; TNode])
  | TTuple ts -> (
      match ts with
      | [t] -> ty_to_sort t
      | ts ->
        let name = OCamlUtils.oget (datatype_name ty) in
        DataTypeSort (name, BatList.map ty_to_sort ts))
  | TOption ty' ->
    let name = OCamlUtils.oget (datatype_name ty) in
    DataTypeSort (name, [ty_to_sort ty'])
  | TMap _ -> failwith "unimplemented"
  (*       mk_array_sort ctx (ty_to_sort ctx ty1) (ty_to_sort ctx ty2)*)
  | TVar _ | QVar _ | TArrow _ | TRecord _ ->
    failwith
      (Printf.sprintf "internal error (ty_to_sort): %s"
         (Nv_lang.Printing.ty_to_string ty))



(** * Utilities *)
(** ** Naming convention of useful variables *)
let label_var i =
  Printf.sprintf "label-%d-" i

let node_of_label_var s =
  int_of_string
    (BatList.nth (BatString.split_on_char '-' s) 1)

let proj_of_var s =
  let (name, _i) = Var.from_var @@ Var.of_var_string s in
  try
    let _, s2 = BatString.split name "-proj-" in
    let s2 = List.hd @@ BatString.split_on_char '-' s2 in
    Some (int_of_string s2)
  with Not_found -> None

let assert_var i =
  Printf.sprintf "assert-%d" i

(* this is flaky, the variable name used by SMT will be
   assert-n-result, we need to chop both ends *)
let node_of_assert_var s =
  int_of_string (BatString.chop ~l:7 ~r:7 s)

let symbolic_of_proj_var s =
  let (name, i) = Var.from_var @@ Var.of_var_string s in
  try
    let s1, _ = BatString.split name "-proj-" in
    Var.to_var (s1, i)
  with
  | Not_found -> Var.to_var (name, i)

let symbolic_var (s: Var.t) =
  Var.to_string s
