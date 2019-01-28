(** * SMT encoding of network *)

open Collections
open Unsigned
open Syntax
open Solution
open SmtUtil
open Profile


(* TODO:
   * make everything an smt_command. i.e. assert, declarations, etc.?
   * Make smt_term wrap around terms, print out more helpful
   comments, include location of ocaml source file
   * Have verbosity levels, we don't always need comments everywhere.
   * Don't hardcode tactics, try psmt (preliminary results were bad),
     consider par-and/par-or once we have multiple problems to solve.*)

(* Classic encodes the SRP as an SMT expression, Functional encodes
   the problem as an NV term which is then translated to SMT *)
type encoding_style = Classic | Functional
                              
type smt_options =
  { mutable verbose        : bool;
    mutable optimize       : bool;
    mutable encoding       : encoding_style;
    mutable unboxing       : bool;
    mutable failures       : int option;
    mutable multiplicities : int Collections.StringMap.t
  }

let smt_config : smt_options =
  { verbose = false;
    optimize = true;
    encoding = Classic;
    unboxing = false;
    failures = None;
    multiplicities = Collections.StringMap.empty
  }

let get_requires_no_failures ds =
  List.filter (fun e -> match e.e with
                        | EOp (AtMost _, _) -> false
                        | _ -> true) (get_requires ds)
  
let get_requires_failures ds =
  List.filter (fun e -> match e.e with
                        | EOp (AtMost _, _) -> true
                        | _ -> false) (get_requires ds)
  |> List.hd
  
let printVerbose (msg: string) (descr: string) (span: Span.t) info =
  let sl =
    match Console.get_position_opt span.start info with
    | Some (sl, _) -> sl
    | _ -> -1
  in
  let fl =
    match Console.get_position_opt span.finish info with
    | Some (fl, _) -> fl
    | _ -> -1
  in
  Printf.sprintf "; %s: %s on %d-%d\n" msg descr sl fl

module SmtLang =
  struct

    type datatype_decl =
      { name         : string;
        params       : sort list;
        constructors : (constructor_decl) list
      }
      
    and constructor_decl =
      { constr_name : string; (** name of constructor *)
        constr_args : (string * sort) list (** projection functions
                                              and their type *)
      }
      
    and sort =
      | BoolSort
      | IntSort
      | MapSort of sort * sort
      | DataTypeSort of string * (sort list)
      | BitVecSort of int
      | VarSort of string
                 
    type smt_term =
      | Int of string (** unbounded integers *)
      | Bool of bool
      | And of smt_term * smt_term
      | Or of smt_term * smt_term
      | Not of smt_term
      | Add of smt_term * smt_term
      | Sub of smt_term * smt_term
      | Eq of smt_term * smt_term
      | Lt of smt_term * smt_term
      | Leq of smt_term * smt_term
      | Ite of smt_term * smt_term * smt_term
      | Var of string
      | Bv of Integer.t
      | AtMost of (smt_term list) * (smt_term list) * smt_term
      | Constructor of string * sort (** constructor name, instantiated sort*)
      | App of smt_term * (smt_term list)
             
    type term =
      { t      : smt_term;
        tdescr : string;
        tloc   : Span.t
      }
      
    type constant =
      { cname  : string;
        csort  : sort;
        cdescr : string;
        cloc   : Span.t
      }

    (* NOTE: Do we want to have constants as commands? Ordering issues
       must be considered. If we want to have all declarations on top. *)
    type smt_command =
      | Echo : string -> smt_command
      | Eval : term -> smt_command
      | Assert : term -> smt_command
      | CheckSat : smt_command
      | GetModel : smt_command
      | Push : smt_command
      | Pop : smt_command

    type command =
      { com      : smt_command;
        comdescr : string;
        comloc   : Span.t
      }

    (** ** Constructors for SMT terms *)
      
    let mk_int_u32 i =
      Int (i |> Integer.to_int |> string_of_int)

    let mk_int i = Int (string_of_int i)

    let mk_bool b = Bool b

    let mk_var s = Var s

    let mk_bv i = Bv i

    let mk_constructor f ts = Constructor (f, ts)
                            
    let mk_app f args =
      App (f, args)

    let mk_and t1 t2 = And (t1, t2)

    let mk_or t1 t2 = Or (t1, t2)

    let mk_not t1 = Not t1

    let mk_add t1 t2 = Add (t1, t2)

    let mk_sub t1 t2 = Sub (t1, t2)

    let mk_eq t1 t2 = Eq (t1, t2)

    let mk_lt t1 t2 = Lt (t1, t2)

    let mk_leq t1 t2 = Leq (t1, t2)

    let mk_ite t1 t2 t3 = Ite (t1, t2, t3)

    let mk_ite_fast t1 t2 t3 =
      match t2,t3 with
      | Bool true, Bool false -> t1
      | Bool false, Bool true -> Not t1
      | Bool true, Bool true -> Bool true
      | Bool false, Bool false -> Bool false
      | _, _ -> mk_ite t1 t2 t3

    let mk_atMost t1 t2 t3 = AtMost (t1, t2, t3)

    let mk_term ?(tdescr="") ?(tloc= Span.default) (t: smt_term) =
      {t; tdescr; tloc}
      
    (** ** Constructors for SMT commands *)

    let mk_echo s = Echo s

    let mk_eval tm = Eval tm

    let mk_assert tm = Assert tm

    let mk_command ?(comdescr ="") ?(comloc=Span.default) (com : smt_command) =
      {com; comdescr; comloc}
      
    (** ** Functions related to datatype constructors *)
      
    let get_constructors decl =
      decl.constructors

    let get_projections (constr: constructor_decl) =
      constr.constr_args

    let get_recognizer (constr : constructor_decl) =
      "is-" ^ constr.constr_name

    (** ** Compilation to SMT-LIB2 *)

    let rec sort_to_smt (s : sort) : string =
      match s with
      | BoolSort -> "Bool"
      | IntSort -> "Int"
      | MapSort (s1, s2) ->
         Printf.sprintf "((%s) %s)" (sort_to_smt s1) (sort_to_smt s2)
      | DataTypeSort (name, ls) ->
         let args = printList sort_to_smt ls "" " " "" in
         Printf.sprintf "(%s %s)" name args
      | BitVecSort _ -> failwith "not yet"
      | VarSort s -> s
                   
    let rec smt_term_to_smt (tm : smt_term) : string =
      match tm with
      | Int s -> s
      | Bool b -> if b then "true" else "false"
      | And (b1, b2) ->
         Printf.sprintf "(and %s %s)" (smt_term_to_smt b1) (smt_term_to_smt b2)
      | Or (b1, b2) ->
         Printf.sprintf "(or %s %s)" (smt_term_to_smt b1) (smt_term_to_smt b2)
      | Not b ->
         Printf.sprintf "(not %s)" (smt_term_to_smt b)
      | Add (n, m) ->
         Printf.sprintf "(+ %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
      | Sub (n, m) ->
         Printf.sprintf "(- %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
      | Eq (n, m) ->
         Printf.sprintf "(= %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
      | Lt (n, m) ->
         Printf.sprintf "(< %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
      | Leq (n, m) ->
         Printf.sprintf "(<= %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)         
      | Ite (t1, t2, t3) ->
         Printf.sprintf "(ite %s %s %s)" (smt_term_to_smt t1) (smt_term_to_smt t2)
                        (smt_term_to_smt t3)
      | Var s -> s
      | Bv _ -> failwith "not yet"
      | AtMost (ts1, ts2, t1) ->
         Printf.sprintf "((_ pble %s %s) %s)"
                        (smt_term_to_smt t1)
                        (printList (fun x -> smt_term_to_smt x) ts2 "" " " "")
                        (printList (fun x -> smt_term_to_smt x) ts1 "" " " "")
      | Constructor (name, sort) -> name
      | App (Constructor (name, sort), ts) when ts = [] ->
         Printf.sprintf "(as %s %s)" name (sort_to_smt sort) 
      | App (t, ts) ->
         let args = printList smt_term_to_smt ts "" " " "" in 
         Printf.sprintf "(%s %s)" (smt_term_to_smt t) args

    let term_to_smt verbose info (tm : term) =
        smt_term_to_smt tm.t

    let term_to_smt_meta verbose info (tm : term) =
      (if verbose then
         printVerbose "Translating expression:" tm.tdescr tm.tloc info
       else "") ^
        smt_term_to_smt tm.t

    let constructor_to_smt (c: constructor_decl) : string =
      match c.constr_args with
      | [] -> c.constr_name
      | (p :: ps) ->
         let constrArgs =
           printList (fun (p,s) ->
               Printf.sprintf "(%s %s)" p (sort_to_smt s)) (p :: ps) "" " " ""
         in
         Printf.sprintf "(%s %s)" c.constr_name constrArgs
         
    let rec type_decl_to_smt (dt: datatype_decl) : string =
      Printf.sprintf "(declare-datatypes %s ((%s %s)))"
                     (printList sort_to_smt dt.params "(" " " ")")
                     dt.name
                     (printList constructor_to_smt dt.constructors "" " " "")
      
    let const_decl_to_smt ?(verbose=false) info const : string =
      (if verbose then
         printVerbose "Constant declared about:" const.cdescr const.cloc info
       else
         "") ^
        Printf.sprintf "(declare-const %s %s)" const.cname
                       (sort_to_smt const.csort)

    let smt_command_to_smt info (comm : smt_command) : string =
      match comm with
      | Echo s ->
         Printf.sprintf "(echo %s)" s
      | Eval tm ->
         Printf.sprintf "(eval %s)" (term_to_smt false info tm)
      | Assert tm ->
         Printf.sprintf "(assert %s)" (term_to_smt false info tm)
      | CheckSat ->
         (* for now i am hardcoding the tactics here. *)
         Printf.sprintf "(check-sat-using (then simplify propagate-values simplify \
                         solve-eqs smt))"
      | GetModel ->
         Printf.sprintf "(get-model)"
      | Push ->
         Printf.sprintf "(push)"
      | Pop ->
         Printf.sprintf "(pop)"

    (* NOTE: this currently ignores the comment/loc of the term inside
       the command. Perhaps we would like to combine them in some way
     *)

    let command_of_term_meta info (comm : command) : string =
      match comm.com with
      | Eval tm | Assert tm ->
         (printVerbose "Translating command:" comm.comdescr comm.comloc info) ^
           printVerbose "Translating command:" tm.tdescr tm.tloc info
      | _ ->
         printVerbose "Translating command:" comm.comdescr comm.comloc info
        
        
    let command_to_smt (verbose : bool) info (com : command) : string =
        smt_command_to_smt info com.com

    let command_to_smt_meta (verbose : bool) info (com : command) : string =
      (if verbose then
         command_of_term_meta info com
       else "") ^ 
        smt_command_to_smt info com.com

    let commands_to_smt (verbose : bool) info (coms : command list) : string =
      printList (fun c -> command_to_smt verbose info c) coms "\n" "\n" "\n"

    type smt_answer =
      UNSAT | SAT | UNKNOWN
      | MODEL of (string, string) BatMap.t
      | OTHER of string

    (* parses the initial reply of the solver *)
    let rec parse_reply (solver: solver_proc) =
      let r = get_reply solver in
      match r with
      | Some "sat" -> SAT
      | Some "unsat" -> UNSAT
      | Some "unknown" -> UNKNOWN
      | None -> OTHER "EOF"
      | Some r -> parse_reply solver

    let rec parse_model (solver: solver_proc) =
      let rs = get_reply_until "end_of_model" solver in
      let rec loop rs model =
        match rs with
        | [] -> MODEL model
        | [v] when v = "end_of_model" ->  MODEL model
        | vname :: rs when (BatString.starts_with vname "Var:") ->
           let vname = BatString.lchop ~n:4 vname in
           let rec grab_vals rs acc =
             match rs with
             | [] -> failwith "expected string"
             | v :: _ when (BatString.starts_with v "Var:") || v = "end_of_model" ->
                (acc, rs)
             | v :: rs' ->
                grab_vals rs' (acc ^ v)
           in
           let vval, rs' = grab_vals rs "" in
           loop rs' (BatMap.add vname vval model)
        | _ ->
           failwith "wrong format"
      in loop rs BatMap.empty
       
  end


open SmtLang

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
  ; mutable symbolics: Syntax.ty_or_exp VarMap.t }

let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n =
  if descr = "" then Var.to_string n
  else Printf.sprintf "%s-%s" descr (Var.to_string n)

(** * Returns the SMT name of a datatype *)
let rec datatype_name (ty : ty) : string option =
  match ty with
  | TVar {contents= Link t} -> datatype_name t
  | TTuple ts -> (
      match ts with
      | [t] -> datatype_name t
      | ts ->
        let len = BatList.length ts in
        Some (Printf.sprintf "Pair%d" len))
  | TOption ty -> Some "Option"
  | _ -> None

(** Returns the SMT name of any type *)
let rec type_name (ty : ty) : string =
  match ty with
  | TVar {contents= Link t} -> type_name t
  | TTuple ts -> (
      match ts with
      | [t] -> type_name t
      | ts ->
        let len = BatList.length ts in
        Printf.sprintf "Pair%d" len)
  | TOption ty -> "Option"
  | TBool -> "Bool"
  | TInt _ -> "Int"
  | TMap _ -> failwith "no maps yet"
  | TArrow _ | TVar _ | QVar _ -> failwith "unsupported type in SMT"

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

let rec ty_to_sort (ty: ty) : sort =
  match ty with
  | TVar {contents= Link t} -> ty_to_sort t
  | TBool -> BoolSort
  | TInt _ -> IntSort
  | TTuple ts -> (
      match ts with
      | [t] -> ty_to_sort t
      | ts ->
        let name = oget (datatype_name ty) in
        DataTypeSort (name, BatList.map ty_to_sort ts))
  | TOption ty' ->
    let name = oget (datatype_name ty) in
    DataTypeSort (name, [ty_to_sort ty'])
  | TMap _ -> failwith "unimplemented"
  (*       mk_array_sort ctx (ty_to_sort ctx ty1) (ty_to_sort ctx ty2)*)
  | TVar _ | QVar _ | TArrow _ ->
     failwith
       (Printf.sprintf "internal error (ty_to_sort): %s"
                       (Printing.ty_to_string ty))

module type ExprEncoding =
  sig
    type 'a t

    (** Translates a [Syntax.ty] to an SMT sort *)
    val ty_to_sorts : ty -> sort t
    val encode_exp_z3 : string -> smt_env -> Syntax.exp -> term t 
    val create_strings : string -> Syntax.ty -> string t
    val create_vars : smt_env -> string -> Syntax.var -> string
    val mk_constant : smt_env -> ?cdescr:string -> ?cloc:Span.t
                      -> string -> sort -> term
    val add_symbolic: smt_env -> Var.t t -> Syntax.ty -> unit
    val lift1: ('a -> 'b) -> 'a t -> 'b t
    val lift2: ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
    val to_list : 'a t -> 'a list
    val combine_term: term t -> term
  end

  
module Boxed: ExprEncoding =
  struct

    type 'a t = 'a
    let lift1 f s = f s
    let lift2 f x y = f x y
    let combine_term t = t

    let create_strings str ty = str
                              
    let create_vars env descr x =
      let name =
        if is_symbolic env.symbolics x then
          begin
            Var.to_string x
          end
        else create_name descr x
      in
      name

    let to_list x = [x]

(** Translates a [Syntax.ty] to an SMT datatype declaration *)
let rec ty_to_type_decl (ty: ty) : datatype_decl =
  match ty with
  | TVar {contents= Link t} -> ty_to_type_decl t
  | TInt _ | TBool -> failwith "not a datatype"
  | TOption _ ->
    let name = datatype_name ty |> oget in
    let param = VarSort "T1" in
    let none = { constr_name = "mkNone"; constr_args = [] } in
    let some = { constr_name = "mkSome"; constr_args = [("getSome", param)]} in
    { name = name; params = [param]; constructors = [none; some]}
  | TTuple ts ->
    let len = BatList.length ts in
    let name = datatype_name ty |> oget in
    let params = BatList.mapi (fun i _ -> VarSort (Printf.sprintf "T%d" i)) ts in
    let mkpair = { constr_name = Printf.sprintf "mkPair%d" len;
                   constr_args =
                     BatList.mapi (fun i _ ->
                         Printf.sprintf "proj%d" i, BatList.nth params i) ts} in
    { name = name; params = params; constructors = [mkpair] }
  | TVar _ | QVar _ | TArrow _ | TMap _ ->
    failwith "not a datatype"

(** Finds the declaration for the datatype of ty if it exists,
    otherwise it creates it and adds it to the env *)
let compute_decl (env : smt_env) ty =
  let name = datatype_name ty in
  match name with
  | None -> None
  | Some name ->
    match StringMap.Exceptionless.find name env.type_decls  with
    | None ->
      let decl = ty_to_type_decl ty in
      env.type_decls <- StringMap.add name decl env.type_decls;
      Some decl
    | Some decl -> Some decl

let add_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  env.const_decls <- ConstantSet.add {cname; csort; cdescr; cloc} env.const_decls

let mk_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  add_constant env ~cdescr:cdescr ~cloc:cloc cname csort;
  (mk_var cname) |> (mk_term ~tdescr:cdescr ~tloc:cloc)

let add_constraint (env : smt_env) (c : term) =
  env.ctx <- (mk_assert c |> mk_command) :: env.ctx

let add_symbolic (env : smt_env) (b: Var.t) (ty: Syntax.ty) =
  env.symbolics <- VarMap.add b (Syntax.Ty ty) env.symbolics

let is_symbolic syms x =
  VarMap.mem x syms

let is_var (tm: SmtLang.term) =
  match tm.t with
  | Var _ -> true
  | _ -> false

    let ty_to_sorts = ty_to_sort

    (** Finds the declaration for the datatype of ty if it exists,
   otherwise it creates it and adds it to the env *)
    let compute_decl (env : smt_env) ty =
      let name = datatype_name ty in
      match name with
      | None -> None
      | Some name -> 
         match StringMap.Exceptionless.find name env.type_decls  with
         | None ->
            let decl = ty_to_type_decl ty in
            env.type_decls <- StringMap.add name decl env.type_decls;
            Some decl
         | Some decl -> Some decl

    let add_symbolic env b ty =
      env.symbolics <- VarMap.add b (Syntax.Ty ty) env.symbolics

    let mk_constant = mk_constant

    let rec encode_exp_z3 descr env (e: exp) : term =
      (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ; *)
      match e.e with
      | EVar x ->
         let name =
           if is_symbolic env.symbolics x then
             begin
               (* Printf.printf "var:%s\n" (Var.to_string x); *)
               Var.to_string x
             end
           else create_name descr x
         in
         (mk_var name) |> (mk_term ~tloc:e.espan)
      | EVal v -> encode_value_z3 descr env v
      | EOp (op, es) -> (
        match (op, es) with
        | Syntax.And, [e1;e2] ->
           let ze1 = encode_exp_z3 descr env e1 in
           let ze2 = encode_exp_z3 descr env e2 in
           mk_and (ze1.t) (ze2.t) |>
             mk_term ~tloc:e.espan
        | Syntax.Or, [e1;e2] ->
           let ze1 = encode_exp_z3 descr env e1 in
           let ze2 = encode_exp_z3 descr env e2 in
           mk_or ze1.t ze2.t |>
             mk_term ~tloc:e.espan
        | Not, _ ->
           let ze = BatList.hd es |> encode_exp_z3 descr env in
           mk_not ze.t |>
             mk_term ~tloc:e.espan
        | Syntax.UAdd _, [e1;e2] ->
           let ze1 = encode_exp_z3 descr env e1 in
           let ze2 = encode_exp_z3 descr env e2 in
           mk_add ze1.t ze2.t |>
             mk_term ~tloc:e.espan
        | Syntax.USub _, [e1;e2] ->
           let ze1 = encode_exp_z3 descr env e1 in
           let ze2 = encode_exp_z3 descr env e2 in
           mk_sub ze1.t ze2.t |>
             mk_term ~tloc:e.espan
        | UEq, [e1;e2] ->
           let ze1 = encode_exp_z3 descr env e1 in
           let ze2 = encode_exp_z3 descr env e2 in
           mk_eq ze1.t ze2.t |>
             mk_term ~tloc:e.espan
        | ULess _, [e1;e2] ->
           let ze1 = encode_exp_z3 descr env e1 in
           let ze2 = encode_exp_z3 descr env e2 in
           mk_lt ze1.t ze2.t |>
             mk_term ~tloc:e.espan
        | ULeq _, [e1;e2] ->
           let ze1 = encode_exp_z3 descr env e1 in
           let ze2 = encode_exp_z3 descr env e2 in
           mk_leq ze1.t ze2.t |>
             mk_term ~tloc:e.espan
        | AtMost _, [e1;e2;e3] -> failwith "not bothering with boxed version for now"
        | MCreate, [e1] ->
           failwith "not implemented"
        | MGet, [e1; e2] ->
           failwith "not implemented"
        | MSet, [e1; e2; e3] ->
           failwith "not implemented"
        | MMap, [{e= EFun {arg= x; argty= ty1; resty= ty2; body= e1}}; e2] ->
           failwith "not implemented yet"
        | MMapFilter, _ 
          | MMerge, _
          | _ -> failwith "internal error (encode_exp_z3)" )
      | EIf (e1, e2, e3) ->
         let ze1 = encode_exp_z3 descr env e1 in
         let ze2 = encode_exp_z3 descr env e2 in
         let ze3 = encode_exp_z3 descr env e3 in
         mk_ite_fast ze1.t ze2.t ze3.t |>
           mk_term ~tloc:e.espan
      | ELet (x, e1, e2) ->
         let xstr = create_name descr x in
         let za = mk_constant env xstr (oget e1.ety |> ty_to_sort)
                              ~cloc:e.espan ~cdescr: (descr ^ "-let") in
         let ze1 = encode_exp_z3 descr env e1 in
         let ze2 = encode_exp_z3 descr env e2 in
         add_constraint env (mk_term (mk_eq za.t ze1.t));
         ze2
      | ETuple es -> (
        let ty = oget e.ety in
        match ty with
        | TTuple ts ->
           let pair_decl = compute_decl env ty |> oget in
           let pair_sort = ty_to_sort ty in
           let zes = BatList.map (fun e -> (encode_exp_z3 descr env e).t) es in
           let f = get_constructors pair_decl |> BatList.hd in
           mk_app (mk_constructor f.constr_name pair_sort) zes |>
             mk_term ~tloc:e.espan
        | _ -> failwith "internal error (encode_exp_z3)" )
      | ESome e1 ->
         let ty = oget e.ety in
         let decl = compute_decl env ty |> oget in
         let sort = ty_to_sort ty in
         let f = BatList.nth (get_constructors decl) 1 in
         let ze = encode_exp_z3 descr env e1 in
         mk_app (mk_constructor f.constr_name sort) [ze.t] |>
           mk_term ~tloc:e.espan
      | EMatch (e, bs) ->
         let ze1 = encode_exp_z3 descr env e in
         (* do not create a new SMT variable if you are matching on a variable *)
         if is_var ze1 then
           encode_branches_z3 descr env ze1 bs (oget e.ety)
         else
           begin
             let name = create_fresh descr "match" in
             let za = mk_constant env name (ty_to_sort (oget e.ety))
                                  ~cdescr:(descr ^ "-match") ~cloc:e.espan in
             add_constraint env (mk_term ~tloc:e.espan (mk_eq za.t ze1.t));
             encode_branches_z3 descr env za bs (oget e.ety)
           end
      | ETy (e, ty) -> encode_exp_z3 descr env e
      | EFun _ | EApp _ -> failwith "function in smt encoding"

    and encode_branches_z3 descr env name bs (t: ty) =
      match BatList.rev bs with
      | [] -> failwith "internal error (encode_branches)"
      | (p, e) :: bs ->
         let ze = encode_exp_z3 descr env e in
         (* we make the last branch fire no matter what *)
         let _ = encode_pattern_z3 descr env name p t in
         encode_branches_aux_z3 descr env name (BatList.rev bs) ze t

    (* I'm assuming here that the cases are exhaustive *)
    and encode_branches_aux_z3 descr env name bs accze (t: ty) =
      match bs with
      | [] -> accze
      | (p, e) :: bs ->
         let ze = encode_exp_z3 descr env e in
         let zp = encode_pattern_z3 descr env name p t in
         let ze = mk_ite_fast zp.t ze.t accze.t |> mk_term in
         encode_branches_aux_z3 descr env name bs ze t

    and encode_pattern_z3 descr env zname p (t: ty) =
      let ty = get_inner_type t in
      match (p, ty) with
      | PWild, _ ->
         mk_bool true |>
           mk_term
      | PVar x, t ->
         let local_name = create_name descr x in
         let za = mk_constant env local_name (ty_to_sort t) in
         add_constraint env (mk_term (mk_eq za.t zname.t));
         mk_bool true |> mk_term
      | PBool b, TBool ->
         mk_eq zname.t (mk_bool b) |>
           mk_term
      | PInt i, TInt _ ->
         let const = mk_int_u32 i in
         mk_eq zname.t const |>
           mk_term
      | PTuple ps, TTuple ts -> (
        match (ps, ts) with
        | [p], [t] -> encode_pattern_z3 descr env zname p t
        | ps, ts ->
           (* old encoding in commented code.
          Would create a new variable for each expression in the tuple.
          New encoding avoids doing that when the expression is a variable *)
           (* let znames = *)
           (*   List.mapi *)
           (*     (fun i t -> *)
           (*       let sort = ty_to_sort t in *)
           (*       ( mk_constant env (Printf.sprintf "elem%d" i |> create_fresh descr) sort *)
           (*       , sort *)
           (*        , t ) ) *)
           (*     ts *)
           (* in *)

           (* if set to false, patterns won't use intermediate variables,
          so far always slower to disable intermediate vars *)
           let tuples_intermediate_vars = true in
           let matches =
             if tuples_intermediate_vars then
               let znames =
                 BatList.map2i
                   (fun i t p ->
                     let sort = ty_to_sort t in
                     ( (match p with
                        | PVar x ->
                           let local_name = create_name descr x in
                           mk_constant env local_name sort
                        | _ ->
                           mk_constant env (Printf.sprintf "elem%d" i |> create_fresh descr) sort)
                     , sort
                     , t ) )
                   ts ps
               in
               let tup_decl = compute_decl env ty |> oget in
               let fs = tup_decl |> get_constructors |> BatList.hd |> get_projections in
               BatList.combine znames fs
               |> BatList.iter (fun ((elem, _, _), (f, _)) ->
                      let e = mk_term (mk_app (mk_var f) [zname.t]) in
                      add_constraint env ((mk_eq elem.t e.t) |> mk_term));
               (* let apps = List.map (fun (f, _) -> *)
               (*                let e = mk_term (mk_app (mk_var f) [zname.t]) in *)
               (*                e) fs *)
               (* in *)
               BatList.map
                 (fun (p, (zname, _, ty)) ->
                   match p with
                   | PVar x -> mk_bool true |> mk_term
                   | _ -> encode_pattern_z3 descr env zname p ty )
                 (BatList.combine ps znames)
                 (* let matches = *)
                 (*   List.mapi *)
                 (*     (fun i (p, app) -> *)
                 (*       encode_pattern_z3 descr env app p (List.nth ts i)) *)
                 (*     (List.combine ps apps) *)
             else
               let znames =
                 BatList.map2i
                   (fun i t p ->  p, t ) ts ps
               in
               let tup_decl = compute_decl env ty |> oget in
               let fs = tup_decl |> get_constructors |> BatList.hd |> get_projections in
               BatList.combine znames fs
               |> BatList.map (fun ((p, ty) , (f, _)) ->
                      let e = mk_term (mk_app (mk_var f) [zname.t]) in
                      encode_pattern_z3 descr env e p ty)
           in
           let f acc e = mk_and acc e.t in
           let b = mk_bool true in
           let base = b in
           (BatList.fold_left f base matches) |> mk_term
      )
      | POption None, TOption _ ->
         let opt_decl = compute_decl env ty |> oget in
         let f = opt_decl |> get_constructors |> BatList.hd |> get_recognizer in
         mk_app (mk_var f) [zname.t] |>
           mk_term
      | POption (Some p), TOption t ->
         let new_name = create_fresh descr "option" in
         let za = mk_constant env new_name (ty_to_sort t) in
         let opt_decl = compute_decl env ty |> oget in
         let some_cons = BatList.nth (opt_decl |> get_constructors) 1 in
         let get_some, _ = some_cons |> get_projections |> BatList.hd in
         let is_some = some_cons |> get_recognizer in
         let e = mk_app (mk_var get_some) [zname.t]in
         add_constraint env (mk_term (mk_eq za.t e));
         let zp = encode_pattern_z3 descr env za p t in
         mk_and (mk_app (mk_var is_some) [zname.t]) zp.t |>
           mk_term
      | _ ->
         Console.error
           (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
                           (Printing.pattern_to_string p)
                           (Printing.ty_to_string (get_inner_type t)))

    and encode_value_z3 descr env (v: Syntax.value) =
      (* Printf.printf "value: %s\n" (Printing.value_to_string v) ; *)
      match v.v with
      | VBool b ->
         mk_bool b |>
           mk_term ~tloc:v.vspan
      | VInt i ->
         mk_int_u32 i |>
           mk_term ~tloc:v.vspan       
      | VTuple vs -> (
        match oget v.vty with
        | TTuple ts ->
           let pair_decl = compute_decl env (oget v.vty) in
           let zes = BatList.map (fun v -> (encode_value_z3 descr env v).t) vs in
           let f = (pair_decl |> oget |> get_constructors |> BatList.hd).constr_name in
           mk_app (mk_constructor f (ty_to_sort (oget v.vty))) zes |>
             mk_term ~tloc:v.vspan
        | _ -> failwith "internal error (encode_value)" )
      | VOption None ->
         let opt_decl = compute_decl env (oget v.vty) in
         let f = (opt_decl |> oget |> get_constructors |> BatList.hd).constr_name in
         let e = mk_app (mk_constructor f (ty_to_sort (oget v.vty))) [] in
         mk_term ~tloc:v.vspan e
      | VOption (Some v1) ->
         let opt_decl = compute_decl env (oget v.vty) in
         let f = (BatList.nth (opt_decl |> oget |> get_constructors) 1).constr_name in
         let zv = encode_value_z3 descr env v1 in
         mk_app (mk_constructor f (ty_to_sort (oget v.vty))) [zv.t] |>
           mk_term ~tloc:v.vspan
      | VClosure _ -> failwith "internal error (closure in smt)"
      | VMap map -> failwith "not doing maps yet"
  end

(** * SMT encoding without SMT-datatypes *)  
module Unboxed : ExprEncoding =
  struct

    type 'a t = 'a list
              
    let proj (i: int) (name: string) =
      Printf.sprintf "%s-proj-%d" name i

    let lift1 (f: 'a -> 'b) (zes1 : 'a list) : 'b list =
      BatList.map (fun ze1 -> f ze1) zes1
      
    let lift2 (f: 'a -> 'b -> 'c) (zes1 : 'a list) (zes2: 'b list) =
      BatList.map2 (fun ze1 ze2 -> f ze1 ze2) zes1 zes2

    exception False
            
    let combine_term l =
      match l with
      | [] -> failwith "empty term"
      | e1 :: l -> 
         let e = try BatList.fold_left
                       (fun acc ze1 ->
                         match ze1.t with
                         | Bool true -> acc
                         | Bool false -> raise False
                         | _ -> mk_and ze1.t acc) e1.t l
                 with False -> mk_bool false
      in
      mk_term e

    let create_strings (str: string) (ty: Syntax.ty) =
      match ty with
      | TTuple ts ->
         BatList.mapi (fun i _ -> proj i str) ts
      | _ -> [str]

    let to_list x = x
                  
    let add_symbolic (env : smt_env) (b: Var.t list) (ty: Syntax.ty) =
      match ty with
      | TTuple ts ->
         BatList.iter2 (fun b ty ->
             env.symbolics <- VarMap.add b (Syntax.Ty ty) env.symbolics) b ts
      | _ ->
         env.symbolics <- VarMap.add (BatList.hd b) (Syntax.Ty ty) env.symbolics

    (** Translates a [Syntax.ty] to a list of SMT sorts *)
    let rec ty_to_sorts (ty: ty) : sort list =
      match ty with
      | TVar {contents= Link t} ->
         ty_to_sorts t
      | TBool -> [BoolSort]
      | TInt _ -> [IntSort]
      | TTuple ts -> (
        match ts with
        | [] -> failwith "empty tuple"
        | [t] -> ty_to_sorts t
        | ts -> BatList.map ty_to_sorts ts |> BatList.concat)
      | TOption _ -> failwith "options should be unboxed"
      | TMap _ -> failwith "unimplemented"
      | TVar _ | QVar _ | TArrow _ ->
         failwith
           (Printf.sprintf "internal error (ty_to_sort): %s"
                           (Printing.ty_to_string ty))
              
    let create_vars (env: smt_env) descr (x: Syntax.var) =
      let name =
        if is_symbolic env.symbolics x then
          begin
            Var.name x
          end
        else create_name descr x
      in
      name
      (* match ty with *)
      (* | TTuple ts -> *)
      (*    List.mapi (fun i _ -> proj i name) ts *)
      (* | _ -> *)
      (*    [name] *)

    let mk_constant =
      mk_constant
    (* lift2 (mk_constant env ~cdescr:cdescr ~cloc:cloc) cnames csorts *)

    let rec map3 f l1 l2 l3 =
      match (l1, l2, l3) with
        ([], [], []) -> []
      | (a1::l1, a2::l2, a3::l3) -> let r = f a1 a2 a3 in r :: map3 f l1 l2 l3
      | (_, _, _) -> invalid_arg "map3"
                   
   let rec encode_exp_z3_single descr env (e: exp) : term =
      match e.e with
      | EVar x ->
         create_vars env descr x
         |> mk_var
         |> (mk_term ~tloc:e.espan)
      | EVal v -> encode_value_z3_single descr env v
      | EOp (op, es) -> (
        match (op, es) with
        | Syntax.And, [e1;e2] when is_value e1 ->
           (match (to_value e1).v with
            | VBool true ->
               encode_exp_z3_single descr env e2
            | VBool false ->
               mk_bool false |> mk_term ~tloc:e.espan
            | _ -> failwith "must be a boolean value")
        | Syntax.And, [e1;e2] when is_value e2 ->
           (match (to_value e2).v with
            | VBool true ->
               encode_exp_z3_single descr env e1
            | VBool false ->
               mk_bool false |> mk_term ~tloc:e.espan
            | _ -> failwith "must be a boolean value")
        | Syntax.And, [e1;e2] ->
           let ze1 = encode_exp_z3_single descr env e1 in
           let ze2 = encode_exp_z3_single descr env e2 in
           mk_and ze1.t ze2.t |> mk_term ~tloc:e.espan
        | Syntax.Or, [e1;e2] ->
           let ze1 = encode_exp_z3_single descr env e1 in
           let ze2 = encode_exp_z3_single descr env e2 in
           mk_or ze1.t ze2.t |> mk_term ~tloc:e.espan
        | Not, [e1] ->
           let ze = encode_exp_z3_single descr env e1 in
           mk_not ze.t |> mk_term ~tloc:e.espan
        | Syntax.UAdd _, [e1;e2] ->
           let ze1 = encode_exp_z3_single descr env e1 in
           let ze2 = encode_exp_z3_single descr env e2 in
           mk_add ze1.t ze2.t |> mk_term ~tloc:e.espan
        | Syntax.USub _, [e1;e2] ->
           let ze1 = encode_exp_z3_single descr env e1 in
           let ze2 = encode_exp_z3_single descr env e2 in
           mk_sub ze1.t ze2.t |> mk_term ~tloc:e.espan
        | UEq, [e1;e2] ->
           let ze1 = encode_exp_z3_single descr env e1 in
           let ze2 = encode_exp_z3_single descr env e2 in
           mk_eq ze1.t ze2.t |> mk_term ~tloc:e.espan
        | ULess _, [e1;e2] ->
           let ze1 = encode_exp_z3_single descr env e1 in
           let ze2 = encode_exp_z3_single descr env e2 in
           mk_lt ze1.t ze2.t |> mk_term ~tloc:e.espan
        | ULeq _, [e1;e2] ->
           let ze1 = encode_exp_z3_single descr env e1 in
           let ze2 = encode_exp_z3_single descr env e2 in
           mk_leq ze1.t ze2.t |> mk_term ~tloc:e.espan
        | AtMost _, [e1;e2;e3] ->
           (match e1.e with
            | ETuple es ->
               let zes =
                 BatList.map (fun e -> (encode_exp_z3_single descr env e).t) es in
               (match e2.e with
                | ETuple es ->
                   let zes2 =
                     BatList.map (fun e -> (encode_exp_z3_single descr env e).t) es
                   in
                   let ze3 = encode_value_z3_single descr env (Syntax.to_value e3) in
                   mk_atMost zes zes2 ze3.t |>
                     mk_term ~tloc:e.espan
                | _ -> failwith "AtMost requires a list of integers as second arg"
               )
            | _ -> failwith "AtMost operator requires a list of boolean variables")
        | MCreate, [e1] ->
           failwith "not implemented"
        | MGet, [e1; e2] ->
           failwith "not implemented"
        | MSet, [e1; e2; e3] ->
           failwith "not implemented"
        | MMap, [{e= EFun {arg= x; argty= ty1; resty= ty2; body= e1}}; e2] ->
           failwith "not implemented yet"
        | MMapFilter, _ 
          | MMerge, _
          | _ -> failwith "internal error (encode_exp_z3)")
      | ETy (e, ty) -> encode_exp_z3_single descr env e
      | _ ->
         (* we always know this is going to be a singleton list *)
         let es = encode_exp_z3 descr env e in
         BatList.hd es

    and encode_exp_z3 descr env (e: exp) : term list =
      match e.e with
      | EOp (op, es) ->
         (match op, es with
          | UEq, [e1;e2] ->
             let ze1 = encode_exp_z3 descr env e1 in
             let ze2 = encode_exp_z3 descr env e2 in
             lift2 (fun ze1 ze2 -> mk_eq ze1.t ze2.t |> mk_term ~tloc:e.espan) ze1 ze2
          | _ -> [encode_exp_z3_single descr env e])
      | EVal v when match v.vty with | Some (TTuple _) -> true | _ -> false ->
         encode_value_z3 descr env v
      | EIf (e1, e2, e3) ->
         let zes1 = encode_exp_z3 descr env e1 in
         let zes2 = encode_exp_z3 descr env e2 in
         let zes3 = encode_exp_z3 descr env e3 in
         let guard = combine_term zes1 in
         lift2 (fun ze2 ze3 -> mk_ite_fast guard.t ze2.t ze3.t |>
                                 mk_term ~tloc:e.espan) zes2 zes3
      | ELet (x, e1, e2) ->
         let ty = (oget e1.ety) in
         let sorts = ty |> ty_to_sort in
         let xs = create_vars env descr x in
         let za = mk_constant env xs sorts ~cloc:e.espan ~cdescr: (descr ^ "-let") in
         let ze1 = encode_exp_z3_single descr env e1 in
         let zes2 = encode_exp_z3 descr env e2 in
         add_constraint env (mk_term (mk_eq za.t ze1.t));
         zes2
      | ETuple es ->
         (* Printf.printf "expr: %s\n" (Syntax.show_exp ~show_meta:false e); *)
         (* List.fold_left (fun acc e -> *)
         (*     (encode_exp_z3 descr env e) @ acc) [] es *)
         lift1 (fun e -> encode_exp_z3 descr env e) es |>
           BatList.concat
      | ESome e1 ->
         failwith "Some should be unboxed"
      | EMatch (e1, bs) ->
         let zes1 = encode_exp_z3 descr env e1 in
         (* intermediate variables no longer help here, probably
            because the expressions are pretty simple in this encoding *)
         encode_branches_z3 descr env zes1 bs (oget e1.ety)
      | ETy (e, ty) -> encode_exp_z3 descr env e
      | EFun _ | EApp _ -> failwith "function in smt encoding"
      | _ ->
         (* Printf.printf "expr: %s\n" (Syntax.show_exp ~show_meta:false e); *)
         [encode_exp_z3_single descr env e]
        
    and encode_branches_z3 descr env names bs (t: ty) =
      match BatList.rev bs with
      | [] -> failwith "internal error (encode_branches)"
      | (p, e) :: _ ->
         let zes = encode_exp_z3 descr env e in
         (* we make the last branch fire no matter what *)
         let _ = encode_pattern_z3 descr env names p t in
         encode_branches_aux_z3 descr env names bs zes t

    (* I'm assuming here that the cases are exhaustive *)
    and encode_branches_aux_z3 descr env names bs acczes (t: ty) =
      match bs with
      | [] -> failwith "empty branch list"
      | [(p,e)] -> acczes (* already included*)
      | (p, e) :: bs ->
         let zes = encode_exp_z3 descr env e in
         let zps = encode_pattern_z3 descr env names p t in
         let guard = combine_term zps in
         let acczes = lift2 (fun ze accze ->
                          mk_ite_fast guard.t ze.t accze.t |>
                                               mk_term ~tloc:e.espan) zes acczes
         in
         encode_branches_aux_z3 descr env names bs acczes t

    and encode_pattern_z3 descr env znames p (t: ty) =
      let ty = get_inner_type t in
      match (p, ty) with
      | PWild, _ ->
         [mk_bool true |> mk_term]
      | PVar x, t ->
         let local_name = create_vars env descr x in
         let sort = ty_to_sort t in
         let zas = mk_constant env local_name sort in
         add_constraint env (mk_term (mk_eq zas.t (BatList.hd znames).t));
         [mk_bool true |> mk_term]
      | PBool b, TBool ->
         [mk_eq (BatList.hd znames).t (mk_bool b) |> mk_term]
      | PInt i, TInt _ ->
         let const = mk_int_u32 i in
         [mk_eq (BatList.hd znames).t const |> mk_term]
      | PTuple ps, TTuple ts -> (
        match (ps, ts) with
        | [p], [t] -> encode_pattern_z3 descr env znames p t
        | ps, ts ->
           (* let psts = (BatList.combine ps ts) in *)
           map3 
             (fun p ty zname ->
               match encode_pattern_z3 descr env [zname] p ty with
               | [pt] -> pt
               | _ -> failwith "expected a single variable") ps ts znames)
      | _ ->
         Console.error
           (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
                           (Printing.pattern_to_string p)
                           (Printing.ty_to_string (get_inner_type t)))

    and encode_value_z3 descr env (v: Syntax.value) : term list =
      match v.v with
      | VTuple vs ->
         BatList.map (fun v -> encode_value_z3_single descr env v) vs
      | _ -> [encode_value_z3_single descr env v]
           
    and encode_value_z3_single descr env (v: Syntax.value) : term =
      match v.v with
      | VBool b ->
         mk_bool b |>
           mk_term ~tloc:v.vspan
      | VInt i ->
         mk_int_u32 i |>
           mk_term ~tloc:v.vspan       
      | VOption _ -> failwith "options should have been unboxed"
      | VTuple _ -> failwith "internal error (check that tuples are flat)"
      | VClosure _ -> failwith "internal error (closure in smt)"
      | VMap map -> failwith "not doing maps yet"
  end

(** * Utilities *)
(** ** Naming convention of useful variables *)
let label_var i =
  Printf.sprintf "label-%d" (Integer.to_int i)

let node_of_label_var s =
  Integer.of_string
    (BatList.nth (BatString.split_on_char '-' s) 1)

let proj_of_var s =
  try
    let _, s2 = BatString.split s "proj" in
    Some (int_of_string
            (BatList.nth (BatString.split_on_char '-' s2) 1))
  with Not_found -> None
                  

let assert_var i =
  Printf.sprintf "assert-%d" (Integer.to_int i)

(* this is flaky, the variable name used by SMT will be
   assert-n-result, we need to chop both ends *)
let node_of_assert_var s =
  Integer.of_string (BatString.lchop ~n:7 s |> BatString.rchop ~n:7)

let symbolic_var (s: Var.t) =
  Var.name s
  
let init_solver ds =
  Var.reset () ;
  let symbolics = get_symbolics ds in
  { ctx = [];
    const_decls = ConstantSet.empty;
    type_decls = StringMap.empty;
    symbolics =
      BatList.fold_left (fun acc (v,e) -> VarMap.add v e acc) VarMap.empty symbolics }

module type Encoding =
  sig
    val encode_z3: declarations -> 'a list -> smt_env
  end
  
module ClassicEncoding (E: ExprEncoding): Encoding =
  struct
    open E

    let add_symbolic_constraints env requires sym_vars =
      (* Declare the symbolic variables: ignore the expression in case of SMT *)
      VarMap.iter
        (fun v e ->
          let names = create_vars env "" v in
          mk_constant env names (ty_to_sort (Syntax.get_ty_from_tyexp e))
                      ~cdescr:"Symbolic variable decl"
          |> ignore ) sym_vars ;
      (* add the require clauses *)
      BatList.iter
        (fun e ->
          let es = encode_exp_z3 "" env e in
          ignore (lift1 (fun e -> add_constraint env e) es)) requires


    let encode_z3_merge str env merge =
      let rec loop merge acc =
        match merge.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
           (match exp.e with
            | EFun _ ->
               loop exp ((x,xty) :: acc)
            | _ ->
               let xstr = BatList.rev_map (fun (x,xty) ->
                            mk_constant env (create_vars env str x) (ty_to_sort xty)
                                        ~cdescr:"" ~cloc:merge.espan )
                                        ((x,xty) :: acc) in
               let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
               let results =
                 lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in     
               let es = encode_exp_z3 str env exp in
               ignore(lift2 (fun e result ->
                          add_constraint env (mk_term (mk_eq result.t e.t))) es results);
               (results, xstr))
        | _ -> failwith "internal error"
      in
      loop merge []

    let encode_z3_trans str env trans =
      let rec loop trans acc =
        match trans.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
         (match exp.e with
          | EFun _ ->
             loop exp ((x,xty) :: acc)
          | _ ->
             let xstr = BatList.rev_map (fun (x,xty) ->
                          mk_constant env (create_vars env str x) (ty_to_sort xty)
                                      ~cdescr:"transfer x argument" ~cloc:trans.espan)
                                      ((x,xty) :: acc) in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results =
               lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in     
             let es = encode_exp_z3 str env exp in
             ignore(lift2 (fun e result ->
                        add_constraint env (mk_term (mk_eq result.t e.t))) es results);
             (results, xstr))
        | _ -> failwith "internal error"
      in
      loop trans []

    let encode_z3_init str env e =
      (* Printf.printf "%s\n" (Printing.exp_to_string e); *)
      (* Printf.printf "%s\n" (Syntax.show_exp ~show_meta:false e); *)
      let names = create_strings (Printf.sprintf "%s-result" str) (oget e.ety) in
      let results =
        lift2 (mk_constant env) names (oget e.ety |> ty_to_sorts) in     
      let es = encode_exp_z3 str env e in
      ignore(lift2 (fun e result ->
                 add_constraint env (mk_term (mk_eq result.t e.t))) es results);
      results

    let encode_z3_assert str env node assertion =
      let rec loop assertion acc =
        match assertion.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
         (match exp.e with
          | EFun _ ->
             loop exp ((x,xty) :: acc)
          | _ ->
             let xstr = BatList.rev_map (fun (x,xty) ->
                            mk_constant env (create_vars env str x) (ty_to_sort xty)
                                        ~cdescr:"assert x argument" ~cloc:assertion.espan )
                                        ((x,xty) :: acc) in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results =
               lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in     
             let es = encode_exp_z3 str env exp in
             ignore(lift2 (fun e result ->
                        add_constraint env (mk_term (mk_eq result.t e.t))) es results);
             (results, xstr))
        | _ -> failwith "internal error"
      in
      loop assertion []

    let encode_z3 (ds: declarations) sym_vars : smt_env =
      let env = init_solver ds in
      let eassert = get_assert ds in
      let emerge, etrans, einit, nodes, edges, aty =
        match
          ( get_merge ds
          , get_trans ds
          , get_init ds
          , get_nodes ds
          , get_edges ds
          , get_attr_type ds )
        with
        | Some emerge, Some etrans, Some einit, Some n, Some es, Some aty ->
           (emerge, etrans, einit, n, es, aty)
        | _ ->
           Console.error
             "missing definition of nodes, edges, merge, trans or init"
      in
      (* map each node to the init result variable *)
      let init_map = ref AdjGraph.VertexMap.empty in
      for i = 0 to Integer.to_int nodes - 1 do
        let einit_i = Interp.interp_partial_fun einit [vint (Integer.of_int i)] in
        (* Printf.printf "%s\n" (Printing.exp_to_string einit); *)
        let init =
          encode_z3_init (Printf.sprintf "init-%d" i) env einit_i
        in
        (* add_constraint env (mk_term (mk_eq n.t (mk_int i))); *)
        init_map := AdjGraph.VertexMap.add (Integer.of_int i) init !init_map
      done ;
      
      (* Map each edge to transfer function result *)
      
      (* incoming_map is a map from vertices to list of incoming edges *)
      let incoming_map = ref AdjGraph.VertexMap.empty in
      (* trans_map maps each edge to the variable that holds the result *)
      let trans_map = ref AdjGraph.EdgeMap.empty in
      (* trans_input_map maps each edge to the incoming message variable *)
      let trans_input_map = ref AdjGraph.EdgeMap.empty in
      BatList.iter
        (fun (i, j) ->
          ( try
              let idxs = AdjGraph.VertexMap.find j !incoming_map in
              incoming_map :=
                AdjGraph.VertexMap.add j ((i, j) :: idxs) !incoming_map
            with _ ->
              incoming_map :=
                AdjGraph.VertexMap.add j [(i, j)] !incoming_map ) ;
          let edge =
            if smt_config.unboxing then
              [avalue ((vint i), Some Typing.node_ty, Span.default);
               avalue ((vint j), Some Typing.node_ty, Span.default)]
            else
              [avalue (vtuple [vint i; vint j],
                       Some Typing.edge_ty, Span.default)] in
          (* Printf.printf "etrans:%s\n" (Printing.exp_to_string etrans); *)
          let etrans_uv = Interp.interp_partial_fun etrans edge in
          let trans, x =
            encode_z3_trans
              (Printf.sprintf "trans-%d-%d" (Integer.to_int i)
                              (Integer.to_int j)) 
              env etrans_uv
          in
          trans_input_map := AdjGraph.EdgeMap.add (i, j) x !trans_input_map ;
          trans_map := AdjGraph.EdgeMap.add (i, j) trans !trans_map )
        edges ;
      
      (* Compute the labelling as the merge of all inputs *)
      let labelling = ref AdjGraph.VertexMap.empty in
      for i = 0 to Integer.to_int nodes - 1 do
        let init = AdjGraph.VertexMap.find (Integer.of_int i) !init_map in
        let in_edges =
          try AdjGraph.VertexMap.find (Integer.of_int i) !incoming_map
          with Not_found -> []
        in
        let node = avalue (vint (Integer.of_int i), Some Typing.node_ty, Span.default) in
        let emerge_i = Interp.interp_partial_fun emerge [node] in
        let idx = ref 0 in
        let merged =
          BatList.fold_left
            (fun acc (x, y) ->
              incr idx ;
              let trans = AdjGraph.EdgeMap.find (x, y) !trans_map in
              let str = Printf.sprintf "merge-%d-%d" i !idx in
              let merge_result, x =
                encode_z3_merge str env emerge_i
              in
              let trans_list = to_list trans in
              let acc_list = to_list acc in
              BatList.iter2 (fun y x -> 
                  add_constraint env (mk_term (mk_eq y.t x.t))) (trans_list @ acc_list) x;
              merge_result )
            init in_edges
        in
        let lbl_i_name = label_var (Integer.of_int i) in
        let lbl_i = create_strings lbl_i_name aty in
        let lbl_iv = lift1 Var.create lbl_i in
        add_symbolic env lbl_iv aty;
        let l = lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s)
                      lbl_iv (ty_to_sorts aty)
        in

        ignore(lift2 (fun l merged ->
                   add_constraint env (mk_term (mk_eq l.t merged.t))) l merged);
        labelling := AdjGraph.VertexMap.add (Integer.of_int i) l !labelling
      done ;
      (* Propagate labels across edges outputs *)
      AdjGraph.EdgeMap.iter
        (fun (i, j) x ->
          let label = AdjGraph.VertexMap.find i !labelling in
          BatList.iter2 (fun label x ->
              add_constraint env (mk_term (mk_eq label.t x.t))) (to_list label) x)
        !trans_input_map ;
      (* add assertions at the end *)
      ( match eassert with
        | None -> ()
        | Some eassert ->
           let all_good = ref (mk_bool true) in
           for i = 0 to Integer.to_int nodes - 1 do
             let label =
               AdjGraph.VertexMap.find (Integer.of_int i) !labelling
             in
             let node = avalue (vint (Integer.of_int i), Some Typing.node_ty, Span.default) in
             let eassert_i = Interp.interp_partial_fun eassert [node] in
             let result, x =
               encode_z3_assert (assert_var (Integer.of_int i)) env (Integer.of_int i) eassert_i
             in
             BatList.iter2 (fun x label ->
                 add_constraint env (mk_term (mk_eq x.t label.t))) x (to_list label);
             let assertion_holds =
               lift1 (fun result -> mk_eq result.t (mk_bool true) |> mk_term) result
               |> combine_term in
             all_good :=
               mk_and !all_good assertion_holds.t
           done ;
           add_constraint env (mk_term (mk_not !all_good))) ;
      (* add the symbolic variable constraints *)
      add_symbolic_constraints env (get_requires ds) (env.symbolics (*@ sym_vars*));
      env
  end

(** * Alternative SMT encoding *)
module FunctionalEncoding (E: ExprEncoding) : Encoding =
  struct
    open E

    let add_symbolic_constraints env requires sym_vars =
      (* Declare the symbolic variables: ignore the expression in case of SMT *)
      VarMap.iter
        (fun v e ->
          let names = create_vars env "" v in
          mk_constant env names (ty_to_sort (Syntax.get_ty_from_tyexp e))
                      ~cdescr:"Symbolic variable decl"
          |> ignore ) sym_vars ;
      (* add the require clauses *)
      BatList.iter
        (fun e ->
          let es = encode_exp_z3 "" env e in
          ignore (lift1 (fun e -> add_constraint env e) es)) requires
      
 let encode_z3_assert str env node assertion =
      let rec loop assertion acc =
        match assertion.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
         (match exp.e with
          | EFun _ ->
             loop exp ((x,xty) :: acc)
          | _ ->
             let acc = BatList.rev acc in
             let xs = BatList.map (fun (x,xty) -> create_vars env str x) acc in
             let xstr = BatList.map (fun x -> mk_constant env x (ty_to_sort xty)
                                    ~cdescr:"assert x argument" ~cloc:assertion.espan ) xs
             in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results =
               lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in     
             let es = encode_exp_z3 str env exp in
             ignore(lift2 (fun e result ->
                        add_constraint env (mk_term (mk_eq result.t e.t))) es results);
             (results, xstr))
        | _ -> failwith "internal error"
      in
      loop assertion []
      
    let node_exp (u: Integer.t) : Syntax.exp =
      aexp(e_val (vint u), Some Typing.node_ty, Span.default)

    let edge_exp (u: Integer.t) (v: Integer.t) : Syntax.exp =
      aexp(e_val (vtuple [vint u; vint v]),
           Some Typing.edge_ty, Span.default)
      
    (** An alternative SMT encoding, where we build an NV expression for
   each label, partially evaluate it and then encode it *)
    let encode_z3 (ds: declarations) sym_vars : smt_env =
      let env = init_solver ds in
      let eassert = get_assert ds in
      let emerge, etrans, einit, nodes, edges, aty =
        match
          ( get_merge ds
          , get_trans ds
          , get_init ds
          , get_nodes ds
          , get_edges ds
          , get_attr_type ds )
        with
        | Some emerge, Some etrans, Some einit, Some n, Some es, Some aty ->
           (emerge, etrans, einit, n, es, aty)
        | _ ->
           Console.error
             "missing definition of nodes, edges, merge, trans or init"
      in
      (* Create a map from nodes to smt variables denoting the label of the node*)
      let labelling =
        AdjGraph.fold_vertices (fun u acc ->
            let lbl_u_name = label_var u in
            let lbl_u = create_strings lbl_u_name aty in
            let lblt =
              lift2 (mk_constant env) lbl_u (ty_to_sorts aty) in            
            add_symbolic env (lift1 Var.create lbl_u) aty;
            AdjGraph.VertexMap.add u lblt acc)
                               nodes AdjGraph.VertexMap.empty
      in

      let init_exp u = eapp einit (node_exp u) in
      let trans_exp u v x = eapp (eapp etrans (edge_exp u v)) x in
      let merge_exp u x y = eapp (eapp (eapp emerge (node_exp u)) x) y in

      (* map from nodes to incoming messages*)
      let incoming_messages_map =
        BatList.fold_left (fun acc (u,v) -> 
            let lblu = aexp (evar (label_var u |> Var.create), Some aty, Span.default) in
            let transuv = trans_exp u v lblu in
            AdjGraph.VertexMap.modify_def [] v (fun us -> transuv :: us) acc)
                       AdjGraph.VertexMap.empty edges
      in

      (* map from nodes to the merged messages *)
      let merged_messages_map =
        AdjGraph.fold_vertices (fun u acc ->
            let messages = AdjGraph.VertexMap.find_default [] u incoming_messages_map in
            let best = BatList.fold_left (fun accm m -> merge_exp u m accm)
                                      (init_exp u) messages
            in
            let str = Printf.sprintf "merge-%d" (Integer.to_int u) in
            let best_smt = Interp.Full.interp_partial best |> encode_exp_z3 str env in
            AdjGraph.VertexMap.add u best_smt acc) nodes AdjGraph.VertexMap.empty
      in

      AdjGraph.fold_vertices (fun u () ->
          let lblu = try AdjGraph.VertexMap.find u labelling
                     with Not_found -> failwith "label variable not found"
          in
          let merged = try AdjGraph.VertexMap.find u merged_messages_map
                       with Not_found -> failwith "merged variable not found"
          in
          ignore(lift2 (fun lblu merged ->
                     add_constraint env (mk_term (mk_eq lblu.t merged.t))) lblu merged))
                             nodes ();
      (* add assertions at the end *)
      (* TODO: same as other encoding make it a function *)
      ( match eassert with
        | None -> ()
        | Some eassert ->
           let all_good = ref (mk_bool true) in
           for i = 0 to Integer.to_int nodes - 1 do
             let label =
               AdjGraph.VertexMap.find (Integer.of_int i) labelling
             in
             let result, x =
               encode_z3_assert (assert_var (Integer.of_int i)) env (Integer.of_int i) eassert
             in
             BatList.iter2 (fun x label ->
                 add_constraint env (mk_term (mk_eq x.t label.t))) x (to_list label);
             let assertion_holds =
               lift1 (fun result -> mk_eq result.t (mk_bool true) |> mk_term) result
               |> combine_term in
             all_good :=
               mk_and !all_good assertion_holds.t
           done ;
           add_constraint env (mk_term (mk_not !all_good))) ;
      (* add the symbolic variable constraints *)
      add_symbolic_constraints env (get_requires ds) (env.symbolics (*@ sym_vars*));
      env
  end
      
    (** ** SMT query optimization *)
    let rec alpha_rename_smt_term (renaming: string StringMap.t) (tm: smt_term) =
      match tm with
      | Int _ | Bool _ | Constructor _ -> tm
      | And (tm1, tm2) ->
         And (alpha_rename_smt_term renaming tm1, alpha_rename_smt_term renaming tm2)
      | Or (tm1, tm2) ->
         Or (alpha_rename_smt_term renaming tm1, alpha_rename_smt_term renaming tm2)
      | Not tm1 ->
         Not (alpha_rename_smt_term renaming tm1)
      | Add (tm1, tm2) ->
         Add (alpha_rename_smt_term renaming tm1, alpha_rename_smt_term renaming tm2)
      | Sub (tm1, tm2) ->
         Sub (alpha_rename_smt_term renaming tm1, alpha_rename_smt_term renaming tm2)
      | Eq (tm1, tm2) ->
         Eq (alpha_rename_smt_term renaming tm1, alpha_rename_smt_term renaming tm2)
      | Lt (tm1, tm2) ->
         Lt (alpha_rename_smt_term renaming tm1, alpha_rename_smt_term renaming tm2)
      | Leq (tm1, tm2) ->
         Leq (alpha_rename_smt_term renaming tm1, alpha_rename_smt_term renaming tm2)
      | Ite (tm1, tm2, tm3) ->
         Ite (alpha_rename_smt_term renaming tm1,
              alpha_rename_smt_term renaming tm2,
              alpha_rename_smt_term renaming tm3)
      | AtMost (tm1, tm2, tm3) ->
         AtMost (BatList.map (alpha_rename_smt_term renaming) tm1,
                 tm2,
                 alpha_rename_smt_term renaming tm3)
      | Var s ->
         (match StringMap.Exceptionless.find s renaming with
          | None -> tm
          | Some x -> Var x)
      | Bv _ -> failwith "not yet"
      | App (tm1, tms) ->
         App (alpha_rename_smt_term renaming tm1,
              BatList.map (alpha_rename_smt_term renaming) tms)
        
    let alpha_rename_term (renaming: string StringMap.t) (tm: term) =
      {tm with t = alpha_rename_smt_term renaming tm.t}
      
    (** Removes all variable equalities *)
    let propagate_eqs (env : smt_env) =
      let updateUnionFind eqSets s =
        try
          StringMap.find s eqSets, eqSets
        with Not_found ->
          let r = BatUref.uref s in
          r, StringMap.add s r eqSets
      in
      (* compute equality classes of variables and remove equalities between variables *)
      let (eqSets, new_ctx) = BatList.fold_left (fun (eqSets, acc) c ->
                                  match c.com with
                                  | Assert tm ->
                                     (match tm.t with
                                      | Eq (tm1, tm2) ->
                                         (match tm1, tm2 with
                                          | Var s1, Var s2 ->
                                             let r1, eqSets = updateUnionFind eqSets s1 in
                                             let r2, eqSets = updateUnionFind eqSets s2 in
                                             BatUref.unite r1 r2;
                                             (eqSets, acc)
                                          | _ -> (eqSets, c :: acc))
                                      | _ -> (eqSets, c :: acc))
                                  | _ -> (eqSets, c :: acc)) (StringMap.empty, []) env.ctx
      in

      let renaming = StringMap.map (fun r -> BatUref.uget r) eqSets in
      (* apply the computed renaming *)
      env.ctx <- BatList.rev_map (fun c ->
                     match c.com with
                     | Assert tm -> {c with com = Assert (alpha_rename_term renaming tm)}
                     | Eval tm -> {c with com = Eval (alpha_rename_term renaming tm)}
                     | _  -> c) new_ctx;
      (* remove unnecessary declarations *)
      (* had to increase stack size to avoid overflow here..
         consider better implementations of this function*)
      env.const_decls <-
        ConstantSet.filter (fun cdecl ->
            try
              let repr = StringMap.find cdecl.cname renaming in
              if repr = cdecl.cname then true else false
            with Not_found -> true) env.const_decls;
      renaming, env
      
    type smt_result = Unsat | Unknown | Sat of Solution.t

    (** Emits the code that evaluates the model returned by Z3. *)  
    let eval_model (symbolics: Syntax.ty_or_exp VarMap.t)
                   (num_nodes: Integer.t)
                   (eassert: Syntax.exp option)
                   (renaming: string StringMap.t) : command list =
      let var x = "Var:" ^ x in
      (* Compute eval statements for labels *)
      (* let labels = *)
      (*   AdjGraph.fold_vertices (fun u acc -> *)
      (*       let lblu = label_var u in *)
      (*       let tm = mk_var (StringMap.find_default lblu lblu renaming) |> mk_term in *)
      (*       let ev = mk_eval tm |> mk_command in *)
      (*       let ec = mk_echo ("\"" ^ (var lblu) ^ "\"") |> mk_command in *)
      (*       ec :: ev :: acc) num_nodes [(mk_echo ("\"end_of_model\"") |> mk_command)] in *)
      let base = [(mk_echo ("\"end_of_model\"") |> mk_command)] in
      (* Compute eval statements for assertions *)
      let assertions =
        match eassert with
        | None -> base
        | Some _ ->
           AdjGraph.fold_vertices (fun u acc ->
               let assu = (assert_var u) ^ "-result" in
               let tm = mk_var (StringMap.find_default assu assu renaming) |> mk_term in
               let ev = mk_eval tm |> mk_command in
               let ec = mk_echo ("\"" ^ (var assu) ^ "\"")
                        |> mk_command in
               ec :: ev :: acc) num_nodes base
      in
      (* Compute eval statements for symbolic variables *)
      let symbols =
        VarMap.fold (fun sv _ acc ->
            let sv = symbolic_var sv in
            let tm = mk_var (StringMap.find_default sv sv renaming) |> mk_term in
            let ev = mk_eval tm |> mk_command in
            let ec = mk_echo ("\"" ^ (var sv) ^ "\"") |> mk_command in
            ec :: ev :: acc) symbolics assertions in
      symbols

    let parse_val (s : string) : Syntax.value =
      let lexbuf = Lexing.from_string s
      in 
      try SMTParser.smtlib SMTLexer.token lexbuf
      with exn ->
        begin
          let tok = Lexing.lexeme lexbuf in
          failwith (Printf.sprintf "failed to parse string %s on %s" s tok)
        end
           
    let translate_model (m : (string, string) BatMap.t) : Solution.t =
      BatMap.foldi (fun k v sol ->
          let nvval = parse_val v in
          match k with
          | k when BatString.starts_with k "label" ->
             {sol with labels= AdjGraph.VertexMap.add (node_of_label_var k) nvval sol.labels}
          | k when BatString.starts_with k "assert-" ->
             {sol with assertions=
                         match sol.assertions with
                         | None ->
                            Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                                         (nvval |> Syntax.bool_of_val |> oget)
                                                         AdjGraph.VertexMap.empty)
                         | Some m ->
                            Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                                         (nvval |> Syntax.bool_of_val |> oget) m)
             }
          | k ->
             {sol with symbolics= Collections.StringMap.add k nvval sol.symbolics}) m
                   {symbolics = StringMap.empty;
                    labels = AdjGraph.VertexMap.empty;
                    assertions= None}

    let box_vals (xs : (int * Syntax.value) list) =
      match xs with
      | [(_,v)] -> v
      | _ ->
         vtuple (BatList.sort (fun (x1,x2) (y1,y2) -> compare x1 y1) xs
                 |> BatList.map (fun (x,y) -> y))

    (* TODO: boxing for symbolic variables as well *)
    let translate_model_unboxed (m : (string, string) BatMap.t) : Solution.t =
      let (symbolics, labels, assertions) =
        BatMap.foldi (fun k v (symbolics, labels, assertions) ->
            let nvval = parse_val v in
            match k with
            | k when BatString.starts_with k "label" ->
               (match proj_of_var k with
                | None ->
                   ( symbolics,
                     AdjGraph.VertexMap.add (node_of_label_var k) [(0,nvval)] labels,
                     assertions )
                  
                | Some i ->
                   ( symbolics,
                     AdjGraph.VertexMap.modify_def
                       [] (node_of_label_var k) (fun xs -> (i,nvval) :: xs) labels,
                     assertions ))
          | k when BatString.starts_with k "assert-" ->
             ( symbolics,
               labels,
               match assertions with
               | None ->
                  Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                               (nvval |> Syntax.bool_of_val |> oget)
                                               AdjGraph.VertexMap.empty)
               | Some m ->
                  Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                               (nvval |> Syntax.bool_of_val |> oget) m) )
          | k ->
             (Collections.StringMap.add k nvval symbolics, labels, assertions)) m
                     (StringMap.empty,AdjGraph.VertexMap.empty, None)
      in
      { symbolics = symbolics;
        labels = AdjGraph.VertexMap.map (box_vals) labels;
        assertions = assertions }
      
    (** ** Translate the environment to SMT-LIB2 *)

      (* TODO: For some reason this version of env_to_smt does not work correctly..
         maybe investigate at some point *)
    (* let env_to_smt ?(verbose=false) info (env : smt_env) = *)
      (* let buf = Buffer.create 8000000 in *)
      (* (\* Emit context *\) *)
      (* Buffer.add_string buf "(set-option :model_evaluator.completion true)"; *)
      (* List.iter (fun c -> Buffer.add_string buf (command_to_smt verbose info c)) env.ctx; *)
      (* ConstantSet.iter (fun c -> *)
      (*     Buffer.add_string buf (const_decl_to_smt ~verbose:verbose info c)) env.const_decls; *)
      (* Buffer.contents buf *)
      
    let env_to_smt ?(verbose=false) info (env : smt_env) =
      let context = BatList.rev_map (fun c -> command_to_smt verbose info c) env.ctx in
      let context = BatString.concat "\n" context in

      (* Emit constants *)
      let constants = ConstantSet.to_list env.const_decls in
      let constants =
        BatString.concat "\n"
                         (BatList.map (fun c -> const_decl_to_smt ~verbose:verbose info c)
                                   constants)
      in
      (* Emit type declarations *)
      let decls = StringMap.bindings env.type_decls in
      let decls = String.concat "\n"
                                (BatList.map (fun (_,typ) -> type_decl_to_smt typ) decls) in
      Printf.sprintf "(set-option :model_evaluator.completion true)
                          \n %s\n %s\n %s\n" decls constants context
    (* this new line is super important otherwise we don't get a reply
      from Z3.. not understanding why*)

    let check_sat info =
      Printf.sprintf "%s\n"
                     ((CheckSat |> mk_command) |> command_to_smt smt_config.verbose info)

    (* Emits the query to a file in the disk *)
    let printQuery (chan: out_channel Lazy.t) (msg: string) =
      let chan = Lazy.force chan in
      Printf.fprintf chan "%s\n%!" msg

    let expr_encoding smt_config =
      match smt_config.unboxing with
      | true -> (module Unboxed : ExprEncoding)
      | false -> (module Boxed : ExprEncoding)

    (* Asks the SMT solver to return a model and translates it to NV lang *)
    let ask_for_model query chan info env solver renaming ds =
      (* build a counterexample based on the model provided by Z3 *)
      let num_nodes =
        match get_nodes ds with
        | Some n -> n
        | _ -> failwith "internal error (encode)"
      in
      let eassert = get_assert ds in
      let model = eval_model env.symbolics num_nodes eassert renaming in
      let model_question = commands_to_smt smt_config.verbose info model in
      ask_solver solver model_question;
      if query then
        printQuery chan model_question;
      let model = solver |> parse_model in
      (match model with
       | MODEL m ->
          if smt_config.unboxing then
            Sat (translate_model_unboxed m)
          else
            Sat (translate_model m)
       | OTHER s ->
          Printf.printf "%s\n" s;
          failwith "failed to parse a model"
       | _ -> failwith "failed to parse a model")

                
    (** Asks the smt solver whether the query was unsat or not
     and returns a model if it was sat.*)
    let get_sat query chan info env solver renaming ds reply =
      ask_solver solver "(get-info :all-statistics)\n
                         (echo \"end stats\")\n";
      let rs = get_reply_until "end stats" solver in
      let rs =
        BatList.filter (fun s -> BatString.starts_with s " :time" ||
                                   BatString.starts_with s " :memory") rs
        |> String.concat "\n"
      in
      Printf.printf "Z3 stats:\n %s\n" rs;
      match reply with
      | UNSAT -> Unsat
      | SAT ->
         ask_for_model query chan info env solver renaming ds
      | UNKNOWN ->
         Unknown
      | _ -> failwith "unexpected answer from solver\n"

    let refineModelMinimizeFailures model info query chan solve renaming env ds =
      match (get_requires_failures ds).e with
      | EOp(AtMost n, [e1;e2;e3]) ->
         (match e1.e with
          | ETuple es ->
             let mult = smt_config.multiplicities in
             let arg2 =
               aexp(etuple (BatList.map (fun evar ->
                                match evar.e with
                                | EVar fvar ->
                                   let n = Collections.StringMap.find (Var.name fvar)
                                             mult in
                                   (exp_of_value
                                      (avalue (vint (Integer.of_int n),
                                               Some (TInt 32),
                                               Span.default)))
                                | _ -> failwith "expected a variable") es),
                    e2.ety,
                    Span.default)
             in
             let new_req =
               aexp (eop (AtMost n) [e1; arg2;e3], Some TBool, Span.default) in
             let zes = Unboxed.encode_exp_z3 "" env new_req in
             let zes_smt =
               Unboxed.(to_list (lift1 (fun ze -> mk_assert ze |> mk_command) zes))
             in
             Some (commands_to_smt smt_config.verbose info zes_smt)
          | _ -> failwith "expected a tuple")
      | _ -> failwith "expected at most"
           
    (** Refines the first model returned by the solver by asking if
       the counter example still holds when failing only the single
       links *)
    (* TODO: Avoid using this until we have support for source nodes in min-cut *)
    let refineModelWithSingles (model : Solution.t) info query chan solve renaming _ ds =
      (* Find and separate the single link failures from the rest *)
      let (failed, notFailed) =
        Collections.StringMap.fold (fun fvar fval (accFailed, accNotFailed) ->
            match fval.v with
            | VBool b ->
               if b then
                 begin
                   let fmult = Collections.StringMap.find fvar smt_config.multiplicities in
                   if fmult > 1 then
                     (accFailed, fvar :: accNotFailed)
                   else
                     (fvar :: accFailed, accNotFailed)
                 end
               else (accFailed, fvar :: accNotFailed)
            | _ -> failwith "This should be a boolean variable") model.symbolics ([], [])
      in
      match failed with
      | [] -> None
      | _ ->
         let failed =
           BatList.map (fun fvar -> (mk_eq (mk_var fvar) (mk_bool true))
                                    |> mk_term |> mk_assert |> mk_command) failed
           |> commands_to_smt smt_config.verbose info
         in
         let notFailed =
           BatList.map (fun fvar -> (mk_eq (mk_var fvar) (mk_bool false))
                                    |> mk_term |> mk_assert |> mk_command) notFailed
           |> commands_to_smt smt_config.verbose info
         in
         Some (failed ^ notFailed)
         
      let refineModel (model : Solution.t) info query chan env solver renaming ds =
        let refiner = refineModelMinimizeFailures in
        match refiner model info query chan solver renaming env ds with
        | None ->
           Console.warning "Model was not refined\n";
           Sat model (* no refinement can occur *)
        | Some q ->
           let checkSat = CheckSat |> mk_command |> command_to_smt smt_config.verbose info in
           let q = Printf.sprintf "%s%s\n" q checkSat in
           if query then
             (printQuery chan q);
           ask_solver solver q;
           let reply = solver |> parse_reply in
           let isSat = get_sat query chan info env solver renaming ds reply in
           (* if the second query was unsat, return the first counterexample *)
           match isSat with
           | Sat newModel ->
              Console.warning "Refined the model";
              isSat
           | _ -> Sat model

    let solve info query chan ?symbolic_vars ?(params=[]) ds =
      let sym_vars =
        match symbolic_vars with None -> [] | Some ls -> ls
      in
      let module ExprEnc = (val expr_encoding smt_config) in
      let module Enc =
        (val (if smt_config.encoding = Classic then
                (module ClassicEncoding(ExprEnc) : Encoding)
              else
                (module FunctionalEncoding(ExprEnc) : Encoding)))
      in
      
      (* compute the encoding of the network *)
      let renaming, env =
        time_profile "Encoding network"
          (fun () -> let env = Enc.encode_z3 ds sym_vars in
                     if smt_config.optimize then propagate_eqs env
                     else StringMap.empty, env)
      in
      (* compile the encoding to SMT-LIB *)
      let smt_encoding =
        time_profile "Compiling query"
          (fun () -> env_to_smt ~verbose:smt_config.verbose info env) in
      (* print query to a file if asked to *)
      if query then
        printQuery chan smt_encoding;
      (* Printf.printf "communicating with solver"; *)
      (* start communication with solver process *)
      let solver = start_solver params in
      ask_solver_blocking solver smt_encoding;
      match smt_config.failures with
      | None ->
         let q = check_sat info in
         if query then
           printQuery chan q;
         ask_solver solver q;
         let reply = solver |> parse_reply in
         get_sat query chan info env solver renaming ds reply
      | Some k ->
         let q = check_sat info in
         if query then
           printQuery chan q;
         (* ask if it is satisfiable *)
         ask_solver solver q;
         let reply = solver |> parse_reply in
         (* check the reply *)
         let isSat = get_sat query chan info env solver renaming ds reply in
         (* In order to minimize refinement iterations, once we get a
            counter-example we try to minimize it by only keeping failures
            on single links. If it works then we found an actual
            counterexample, otherwise we refine using the first
            counterexample. *)       
         match isSat with
         | Unsat -> Unsat
         | Unknown -> Unknown
         | Sat model1 ->
            refineModel model1 info query chan env solver renaming ds
          
      
