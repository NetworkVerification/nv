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
    mutable multiplicities : int AdjGraph.EdgeMap.t
  }

let smt_config : smt_options =
  { verbose = false;
    optimize = true;
    encoding = Classic;
    unboxing = false;
    failures = None;
    multiplicites = AdjGraph.EdgeMap.empty
  }

let get_requires_no_failures ds =
  BatList.filter (fun e -> match e.e with
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
      
    type sort =
      | BoolSort
      | IntSort
      | MapSort of sort * sort
      (* | VarSort of string *)
                 
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
      | AtMost of (smt_term list) * smt_term
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

    let mk_atMost t1 t2 = AtMost (t1, t2)

    let mk_term ?(tdescr="") ?(tloc= Span.default) (t: smt_term) =
      {t; tdescr; tloc}
      
    (** ** Constructors for SMT commands *)

    let mk_echo s = Echo s

    let mk_eval tm = Eval tm

    let mk_assert tm = Assert tm

    let mk_command ?(comdescr ="") ?(comloc=Span.default) (com : smt_command) =
      {com; comdescr; comloc}
      
    (** ** Compilation to SMT-LIB2 *)

    let rec sort_to_smt (s : sort) : string =
      match s with
      | BoolSort -> "Bool"
      | IntSort -> "Int"
      | MapSort (s1, s2) ->
         Printf.sprintf "((%s) %s)" (sort_to_smt s1) (sort_to_smt s2)
      (* | VarSort s -> s *)
                   
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
      | AtMost (ts, t1) ->
         Printf.sprintf "((_ pble %s %s) %s)"
                        (smt_term_to_smt t1)
                        (printList (fun _ -> "1") ts "" " " "")
                        (printList (fun x -> smt_term_to_smt x) ts "" " " "")
      | App (t, ts) ->
         let args = printList smt_term_to_smt ts "" " " "" in 
         Printf.sprintf "(%s %s)" (smt_term_to_smt t) args

    let term_to_smt verbose info (tm : term) =
        smt_term_to_smt tm.t
      
    (* let const_decl_to_smt ?(verbose=false) info const : string = *)
    (*   (if verbose then *)
    (*      printVerbose "Constant declared about:" const.cdescr const.cloc info *)
    (*    else *)
    (*      "") ^ *)
    (*     Printf.sprintf "(declare-const %s %s)" const.cname *)
    (*                    (sort_to_smt const.csort) *)

    let const_decl_to_smt const : string =
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
         Printf.sprintf "(check-sat-using (then propagate-values simplify \
                         solve-eqs psmt))"
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
      | UNSAT | SAT | UNKNOWN
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
  { ctx: command list
  ; const_decls: ConstantSet.t (** named constant and its sort *)
  ; symbolics: Syntax.ty_or_exp VarMap.t }

let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n =
  if descr = "" then Var.to_string n
  else Printf.sprintf "%s-%s" descr (Var.to_string n)

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
  {env with const_decls = ConstantSet.add {cname; csort; cdescr; cloc} env.const_decls}

let mk_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  let env = add_constant env ~cdescr:cdescr ~cloc:cloc cname csort in
  ((mk_var cname) |> (mk_term ~tdescr:cdescr ~tloc:cloc), env)
  
let add_constraint (env : smt_env) (c : term) =
  {env with ctx = (mk_assert c |> mk_command) :: env.ctx}

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
  | TMap (ty1,ty2) ->
     MapSort (ty_to_sort ty1, ty_to_sort ty2)
  (*       mk_array_sort ctx (ty_to_sort ctx ty1) (ty_to_sort ctx ty2)*)
  | TVar _ | QVar _ | TArrow _ | _ ->
     failwith
       (Printf.sprintf "internal error (ty_to_sort): %s"
                       (Printing.ty_to_string ty))

module type ExprEncoding =
  sig
    type 'a t

    (** Translates a [Syntax.ty] to an SMT sort *)
    val ty_to_sorts : ty -> sort t
    val encode_exp_z3 : string -> smt_env -> Syntax.exp -> term t  * smt_env
    val create_strings : string -> Syntax.ty -> string t
    val create_vars : smt_env -> string -> Syntax.var -> string
    val add_symbolic: smt_env -> Var.t t -> Syntax.ty -> smt_env
    val lift1: ('a -> 'b) -> 'a t -> 'b t
    val lift2: ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
    val to_list : 'a t -> 'a list
    val of_list : 'a list -> 'a t
    val reduce: ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    val reduce2: ('a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c
    val combine_term: term t -> term
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

    let reduce (f: 'a -> 'b -> 'b) (zes1 : 'a list) (base: 'b) : 'b =
      BatList.fold_right (fun ze1 b -> f ze1 b) zes1 base

    let reduce2 (f: 'a -> 'b -> 'c -> 'c) (zes1 : 'a list)
                (zes2 : 'b list) (base: 'c) : 'c =
      BatList.fold_right2 (fun ze1 ze2 b -> f ze1 ze2 b) zes1 zes2 base
      
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

    let of_list x = x
                  
    let add_symbolic (env : smt_env) (b: Var.t list) (ty: Syntax.ty) =
      match ty with
      | TTuple ts ->
         BatList.fold_left2 (fun env b ty ->
             {env with symbolics=VarMap.add b (Syntax.Ty ty) env.symbolics}) env b ts
      | _ ->
         {env with symbolics=VarMap.add (List.hd b) (Syntax.Ty ty) env.symbolics}

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
      | TMap (ty1,ty2) ->
         (* for now does not work with pairs *)
         let s1 = ty_to_sorts ty1 in
         let s2 = ty_to_sorts ty2 in
         [MapSort (List.hd s1, List.hd s2)]
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

    let rec map3 f l1 l2 l3 =
      match (l1, l2, l3) with
        ([], [], []) -> []
      | (a1::l1, a2::l2, a3::l3) -> let r = f a1 a2 a3 in r :: map3 f l1 l2 l3
      | (_, _, _) -> invalid_arg "map3"

    let rec fold_right3 f l1 l2 l3 accu =
      match (l1, l2, l3) with
        ([], [], []) -> accu
      | (a1::l1, a2::l2, a3::l3) -> f a1 a2 a3 (fold_right3 f l1 l2 l3 accu)
      | (_, _, _) -> invalid_arg "fold_right3"
                   
   let rec encode_exp_z3_single descr env (e: exp) : term * smt_env =
      match e.e with
      | EVar x ->
         (create_vars env descr x
          |> mk_var
          |> (mk_term ~tloc:e.espan), env)
      | EVal v -> encode_value_z3_single descr env v, env
      | EOp (op, es) -> (
        match (op, es) with
        | Syntax.And, [e1;e2] when is_value e1 ->
           (match (to_value e1).v with
            | VBool true ->
               encode_exp_z3_single descr env e2
            | VBool false ->
               mk_bool false |> mk_term ~tloc:e.espan, env
            | _ -> failwith "must be a boolean value")
        | Syntax.And, [e1;e2] when is_value e2 ->
           (match (to_value e2).v with
            | VBool true ->
               encode_exp_z3_single descr env e1
            | VBool false ->
               mk_bool false |> mk_term ~tloc:e.espan, env
            | _ -> failwith "must be a boolean value")
        | Syntax.And, [e1;e2] ->
           let ze1, env1 = encode_exp_z3_single descr env e1 in
           let ze2, env2 = encode_exp_z3_single descr env1 e2 in
           mk_and ze1.t ze2.t |> mk_term ~tloc:e.espan, env2
        | Syntax.Or, [e1;e2] ->
           let ze1, env1 = encode_exp_z3_single descr env e1 in
           let ze2, env2 = encode_exp_z3_single descr env1 e2 in
           mk_or ze1.t ze2.t |> mk_term ~tloc:e.espan, env2
        | Not, [e1] ->
           let ze, env1 = encode_exp_z3_single descr env e1 in
           mk_not ze.t |> mk_term ~tloc:e.espan, env1
        | Syntax.UAdd _, [e1;e2] ->
           let ze1, env1 = encode_exp_z3_single descr env e1 in
           let ze2, env2 = encode_exp_z3_single descr env1 e2 in
           mk_add ze1.t ze2.t |> mk_term ~tloc:e.espan, env2
        | Syntax.USub _, [e1;e2] ->
           let ze1, env1 = encode_exp_z3_single descr env e1 in
           let ze2, env2 = encode_exp_z3_single descr env1 e2 in
           mk_sub ze1.t ze2.t |> mk_term ~tloc:e.espan, env2
        | UEq, [e1;e2] ->
           let ze1, env1 = encode_exp_z3_single descr env e1 in
           let ze2, env2 = encode_exp_z3_single descr env1 e2 in
           mk_eq ze1.t ze2.t |> mk_term ~tloc:e.espan, env2
        | ULess _, [e1;e2] ->
           let ze1, env1 = encode_exp_z3_single descr env e1 in
           let ze2, env2 = encode_exp_z3_single descr env1 e2 in
           mk_lt ze1.t ze2.t |> mk_term ~tloc:e.espan, env2
        | ULeq _, [e1;e2] ->
           let ze1, env1 = encode_exp_z3_single descr env e1 in
           let ze2, env2 = encode_exp_z3_single descr env1 e2 in
           mk_leq ze1.t ze2.t |> mk_term ~tloc:e.espan, env2
        | AtMost _, [e1;e2] ->
           (match e1.e with
            | ETuple es ->
               let zes, env1 =
                 BatList.fold_right
                   (fun e (zes, env) ->
                     let e1, env1 = encode_exp_z3_single descr env e in
                     (e1.t :: zes, env1)) es ([], env) in
               let ze2 = encode_value_z3_single descr env1 (Syntax.to_value e2) in
               mk_atMost zes ze2.t |>
               mk_term ~tloc:e.espan, env1
            | _ -> failwith "AtMost operator requires a list of boolean variables")
        | MCreate, [e1]  ->
           (* let mty = get_inner_type (oget e.ety) in *)
           (*    (match mty with *)
        (*     | TMap (kty, _) -> *)
        (*        let ze1, env = encode_exp_z3_single descr env e1 in *)
        (*        let ksort = ty_to_sort kty in *)
        (*        let msort = ty_to_sort mty in *)
        (*        let kvar = create_vars env descr (Var.fresh "k") in *)
        (*        let mvar = create_vars env descr (Var.fresh "fmap") in *)
        (*        let zk, env = mk_constant env kvar ksort ~cloc:e.espan ~cdescr:descr in *)
        (*        let zm, env = mk_constant env mvar msort ~cloc:e.espan ~cdescr:descr in *)
        (*        let env = *)
        (*          add_constraint env (mk_term (mk_eq (mk_app zm.t [zk.t]) ze1.t)) *)
        (*        in *)
        (*        zm, env *)
        (*     | _ -> failwith "runtime error: missing map key type") *)
        (* | MGet, [emap;ekey] -> *)
        (*    let ze1, env = encode_exp_z3_single descr env emap in *)
        (*    let ze2, env = encode_exp_z3_single descr env ekey in *)
        (*    mk_app ze1.t [ze2.t] |> *)
        (*      mk_term ~tloc:e.espan, env *)
        (* | MSet, [emap; ekey; eval] -> *)
        (*    let mty = get_inner_type (oget e.ety) in *)
        (*    (match mty with *)
        (*     | TMap (kty, _) -> *)
        (*        let ze1, env = encode_exp_z3_single descr env emap in *)
        (*        let ze2, env = encode_exp_z3_single descr env ekey in *)
        (*        let ze3, env = encode_exp_z3_single descr env eval in *)
        (*        let mty = get_inner_type (oget e.ety) in *)
        (*        let msort = ty_to_sort mty in *)
        (*        let ksort = ty_to_sort kty in *)
        (*        let kvar = create_vars env descr (Var.fresh "k") in *)
        (*        let mvar = create_vars env descr (Var.fresh "fmap") in *)
        (*        let zk, env = mk_constant env kvar ksort ~cloc:e.espan ~cdescr:descr in *)
        (*        let zm, env = mk_constant env mvar msort ~cloc:e.espan ~cdescr:descr in *)
        (*        (\* if the key is equal to ekey then the new map returns the new value. *)
        (*           for all other keys, else the new map returns the previous value *\) *)
        (*        let env = *)
        (*          add_constraint env (mk_term (mk_ite (mk_eq zk.t ze2.t) *)
        (*                                              (mk_eq (mk_app zm.t [zk.t]) ze3.t) *)
        (*                                              (mk_eq (mk_app zm.t [zk.t]) *)
        (*                                                     (mk_app ze1.t [zk.t])))) *)
        (*        in *)
        (*        zm, env *)
           failwith "runtime error: missing map key type"
        | MMap, _ ->
           failwith "not implemented yet"
        | MMapFilter, _ 
          | MMerge, _
          | _ -> failwith "internal error (encode_exp_z3)")
      | ETy (e, ty) -> encode_exp_z3_single descr env e
      | _ ->
         (* we always know this is going to be a singleton list *)
         let es, env1 = encode_exp_z3 descr env e in
         List.hd es, env1

    and encode_exp_z3 descr env (e: exp) : term list * smt_env =
      match e.e with
      | EOp (op, es) ->
         (match op, es with
          | UEq, [e1;e2] ->
             let ze1, env1 = encode_exp_z3 descr env e1 in
             let ze2, env2 = encode_exp_z3 descr env1 e2 in
             lift2 (fun ze1 ze2 -> mk_eq ze1.t ze2.t |> mk_term ~tloc:e.espan) ze1 ze2,
             env2
          | _ -> let ze, env1 = encode_exp_z3_single descr env e in
                 [ze], env1)
      | EVal v when (match v.vty with | Some (TTuple _) -> true | _ -> false) ->
         encode_value_z3 descr env v, env
      | EIf (e1, e2, e3) ->
         let zes1, env1 = encode_exp_z3 descr env e1 in
         let zes2, env2 = encode_exp_z3 descr env1 e2 in
         let zes3, env3 = encode_exp_z3 descr env2 e3 in
         let guard = combine_term zes1 in
         lift2 (fun ze2 ze3 -> mk_ite_fast guard.t ze2.t ze3.t |>
                                 mk_term ~tloc:e.espan) zes2 zes3, env3
      | ELet (x, e1, e2) ->
         let ty = (oget e1.ety) in
         let sorts = ty |> ty_to_sort in
         let xs = create_vars env descr x in
         let za, env = mk_constant env xs sorts ~cloc:e.espan ~cdescr: (descr ^ "-let") in
         let ze1, env1 = encode_exp_z3_single descr env e1 in
         let zes2, env2 = encode_exp_z3 descr env1 e2 in
         let env3 = add_constraint env2 (mk_term (mk_eq za.t ze1.t)) in
         zes2, env3
      | ETuple es ->
         BatList.fold_right (fun e (zes, env) ->
             let ze, env1 = encode_exp_z3 descr env e in
             (BatList.append ze zes, env1)) es ([], env)
      | ESome e1 ->
         failwith "Some should be unboxed"
      | EMatch (e1, bs) ->
         let zes1, env1 = encode_exp_z3 descr env e1 in
         (* intermediate variables no longer help here, probably
            because the expressions are pretty simple in this encoding *)
         encode_branches_z3 descr env1 zes1 bs (oget e1.ety)
      | ETy (e, ty) -> encode_exp_z3 descr env e
      | EFun _ | EApp _ -> failwith "function in smt encoding"
      | _ ->
         (* Printf.printf "expr: %s\n" (Syntax.show_exp ~show_meta:false e); *)
         let ze, env = encode_exp_z3_single descr env e in
         [ze], env
        
    and encode_branches_z3 descr env names bs (t: ty) =
      match BatList.rev bs with
      | [] -> failwith "internal error (encode_branches)"
      | (p, e) :: _ ->
         let zes, env1 = encode_exp_z3 descr env e in
         (* we make the last branch fire no matter what *)
         let _, env2 = encode_pattern_z3 descr env1 names p t in
         encode_branches_aux_z3 descr env2 names bs zes t

    (* I'm assuming here that the cases are exhaustive *)
    and encode_branches_aux_z3 descr env names bs acczes (t: ty) =
      match bs with
      | [] -> failwith "empty branch list"
      | [(p,e)] -> acczes, env (* already included*)
      | (p, e) :: bs ->
         let zes, env1 = encode_exp_z3 descr env e in
         let zps, env2 = encode_pattern_z3 descr env1 names p t in
         let guard = combine_term zps in
         let acczes = lift2 (fun ze accze ->
                          mk_ite_fast guard.t ze.t accze.t |>
                                               mk_term ~tloc:e.espan) zes acczes
         in
         encode_branches_aux_z3 descr env2 names bs acczes t

    and encode_pattern_z3 descr env znames p (t: ty) =
      let ty = get_inner_type t in
      match (p, ty) with
      | PWild, _ ->
         [mk_bool true |> mk_term], env
      | PVar x, t ->
         let local_name = create_vars env descr x in
         let sort = ty_to_sort t in
         let zas, env1 = mk_constant env local_name sort in
         [mk_bool true |> mk_term],
         add_constraint env1 (mk_term (mk_eq zas.t (List.hd znames).t))
      | PBool b, TBool ->
         [mk_eq (List.hd znames).t (mk_bool b) |> mk_term], env
      | PInt i, TInt _ ->
         let const = mk_int_u32 i in
         [mk_eq (List.hd znames).t const |> mk_term], env
      | PTuple ps, TTuple ts -> (
        match (ps, ts) with
        | [p], [t] -> encode_pattern_z3 descr env znames p t
        | ps, ts ->
           fold_right3 
             (fun p ty zname (pts, env) ->
               let pt, env = encode_pattern_z3 descr env [zname] p ty in
               (* pt should be singleton *)
               ((List.hd pt) :: pts, env))  ps ts znames ([], env))
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
            (List.nth (BatString.split_on_char '-' s2) 1))
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
    symbolics =
      BatList.fold_left (fun acc (v,e) -> VarMap.add v e acc) VarMap.empty symbolics }

module type Encoding =
  sig
    val encode_z3: declarations -> 'a list -> smt_env
  end
  
module ClassicEncoding (E: ExprEncoding): Encoding =
  struct
    open E

    let add_symbolic_constraints env requires sym_vars : smt_env =
      (* Declare the symbolic variables: ignore the expression in case of SMT *)
      let env1 =
        VarMap.fold
          (fun v e env ->
            let names = create_vars env "" v in
            let _, env = mk_constant env names (ty_to_sort (Syntax.get_ty_from_tyexp e))
                                     ~cdescr:"Symbolic variable decl"
            in env) sym_vars env
      in
      (* add the require clauses *)
      BatList.fold_left
        (fun env e ->
          let es, env = encode_exp_z3 "" env e in
          reduce (fun e env -> add_constraint env e) es env) env1 requires

    let encode_z3_merge str env merge =
      let rec loop merge acc =
        match merge.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
           (match exp.e with
            | EFun _ ->
               loop exp ((x,xty) :: acc)
            | _ ->
               (* xstr arguments are in reverse order due to loop, use
                fold_left instead of fold_right *)
               let xstr, env1 =
                 BatList.fold_left (fun  (xstrs, env) (x,xty) ->
                     let xstr, env1 = mk_constant env (create_vars env str x) (ty_to_sort xty)
                                                  ~cdescr:"" ~cloc:merge.espan
                     in
                   (xstr :: xstrs, env1)) ([], env) ((x,xty) :: acc) in
               let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
               let results, env =
                 reduce2 (fun name sort (results, env) ->
                     let res, env = mk_constant env name sort in
                     (res :: results, env)) names (oget exp.ety |> ty_to_sorts) ([], env1)
               in     
               let es, env = encode_exp_z3 str env exp in
               let env =
                 BatList.fold_right2 (fun e result env ->
                     add_constraint env (mk_term (mk_eq result.t e.t)))
                                     (to_list es) results env in
               (results, xstr, env))
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
             (* xstr arguments are in reverse order due to loop, use
                fold_left instead of fold_right *)
             let xstr, env1 =
               BatList.fold_left (fun (xstrs, env) (x,xty) ->
                   let xstr, env = mk_constant env (create_vars env str x) (ty_to_sort xty)
                                               ~cdescr:"transfer x argument" ~cloc:trans.espan
                   in
                   (xstr :: xstrs, env)) ([], env) ((x,xty) :: acc) in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results, env =
               reduce2 (fun name sort (results, env) ->
                   let res, env = mk_constant env name sort in
                   (res :: results, env)) names (oget exp.ety |> ty_to_sorts) ([], env1)
             in
             let es, env = encode_exp_z3 str env exp in
             let env =
               BatList.fold_right2 (fun e result env ->
                   add_constraint env (mk_term (mk_eq result.t e.t)))
                                   (to_list es) results env in
             (results, xstr, env))
        | _ -> failwith "internal error"
      in
      loop trans []

    let encode_z3_init str env e =
      let names = create_strings (Printf.sprintf "%s-result" str) (oget e.ety) in
      let results, env =
        reduce2 (fun name sort (results, env) ->
            let res, env = mk_constant env name sort in
            (res :: results, env)) names (oget e.ety |> ty_to_sorts) ([], env)
      in     
      let es, env = encode_exp_z3 str env e in
      let env =
        BatList.fold_right2 (fun e result env ->
            add_constraint env (mk_term (mk_eq result.t e.t)))
                            (to_list es) results env in
      (results, env)

    let encode_z3_assert str env node assertion =
      let rec loop assertion acc =
        match assertion.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
         (match exp.e with
          | EFun _ ->
             loop exp ((x,xty) :: acc)
          | _ ->
             let xstr, env1 =
               BatList.fold_left (fun (xstrs, env) (x,xty) ->
                   let xstr, env = mk_constant env (create_vars env str x) (ty_to_sort xty)
                                               ~cdescr:"assert x argument" ~cloc:assertion.espan
                   in
                   (xstr :: xstrs, env)) ([], env) ((x,xty) :: acc)  in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results, env =
               reduce2 (fun name sort (results, env) ->
                   let res, env = mk_constant env name sort in
                   (res :: results, env)) names (oget exp.ety |> ty_to_sorts) ([], env1)
             in
             let es, env = encode_exp_z3 str env exp in
             let env =
               BatList.fold_right2 (fun e result env ->
                   add_constraint env (mk_term (mk_eq result.t e.t)))
                                   (to_list es) results env in
             (results, xstr, env))
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
      let init_map, env =
        AdjGraph.fold_vertices
          (fun i (init_map, env) ->
            let einit_i = Interp.interp_partial_fun einit [vint i] in
            let init, env =
              encode_z3_init (Printf.sprintf "init-%d" (Integer.to_int i)) env einit_i in
            (AdjGraph.VertexMap.add i init init_map, env))
          nodes (AdjGraph.VertexMap.empty, env)
      in
      (* Map each edge to transfer function result *)
      (* incoming_map is a map from vertices to list of incoming edges *)
      let incoming_map = AdjGraph.VertexMap.empty in
      (* trans_map maps each edge to the variable that holds the result *)
      let trans_map = AdjGraph.EdgeMap.empty in
      (* trans_input_map maps each edge to the incoming message variable *)
      let trans_input_map = AdjGraph.EdgeMap.empty in
      let (incoming_map, trans_map, trans_input_map, env) =
        BatList.fold_left (fun (incoming_map, trans_map, trans_input_map, env) (i,j) ->
            let incoming_map =
              match AdjGraph.VertexMap.Exceptionless.find j incoming_map with
              | None ->
                 AdjGraph.VertexMap.add j [(i, j)] incoming_map
              | Some idxs ->
                 AdjGraph.VertexMap.add j ((i, j) :: idxs) incoming_map
            in
            let edge =
              if smt_config.unboxing then
                [avalue ((vint i), Some Typing.node_ty, Span.default);
                 avalue ((vint j), Some Typing.node_ty, Span.default)]
              else
                [avalue (vtuple [vint i; vint j],
                         Some Typing.edge_ty, Span.default)] in
            let etrans_uv = Interp.interp_partial_fun etrans edge in
            (* Printf.printf "%s: %s\n\n\n\n\n" (AdjGraph.printEdge (i,j)) *)
            (*               (Printing.exp_to_string etrans_uv); *)
            let trans, x, env =
              encode_z3_trans
                (Printf.sprintf "trans-%d-%d" (Integer.to_int i)
                                (Integer.to_int j))
                env etrans_uv
            in
            (* List.iter (fun tm -> Printf.printf "%s\n" ( term_to_smt 0 0 tm)) x; *)
            let trans_input_map = AdjGraph.EdgeMap.add (i, j) x trans_input_map in
            let trans_map = AdjGraph.EdgeMap.add (i, j) trans trans_map in
            (incoming_map, trans_map, trans_input_map, env))
                          (incoming_map, trans_map, trans_input_map, env) edges

        (* BatList.fold_right (fun (i,j) (incoming_map, trans_map, trans_input_map, env)->  *)
        (*     let incoming_map =  *)
        (*       match AdjGraph.VertexMap.Exceptionless.find j incoming_map with *)
        (*       | None -> *)
        (*          AdjGraph.VertexMap.add j [(i, j)] incoming_map *)
        (*       | Some idxs -> *)
        (*          AdjGraph.VertexMap.add j ((i, j) :: idxs) incoming_map *)
        (*     in *)
        (*     let edge = *)
        (*       if smt_config.unboxing then *)
        (*         [avalue ((vint i), Some Typing.node_ty, Span.default); *)
        (*          avalue ((vint j), Some Typing.node_ty, Span.default)] *)
        (*       else *)
        (*         [avalue (vtuple [vint i; vint j], *)
        (*                  Some Typing.edge_ty, Span.default)] in *)
        (*     let etrans_uv = Interp.interp_partial_fun etrans edge in *)
        (*     (\* Printf.printf "%s: %s\n\n\n\n\n" (AdjGraph.printEdge (i,j)) *\) *)
        (*     (\*               (Printing.exp_to_string etrans_uv); *\) *)
        (*     let trans, x, env = *)
        (*       encode_z3_trans *)
        (*         (Printf.sprintf "trans-%d-%d" (Integer.to_int i) *)
        (*                         (Integer.to_int j))  *)
        (*         env etrans_uv *)
        (*     in *)
        (*     (\* List.iter (fun tm -> Printf.printf "%s\n" ( term_to_smt 0 0 tm)) x; *\) *)
        (*     let trans_input_map = AdjGraph.EdgeMap.add (i, j) x trans_input_map in *)
        (*     let trans_map = AdjGraph.EdgeMap.add (i, j) trans trans_map in *)
        (*     (incoming_map, trans_map, trans_input_map, env)) *)
                          (*                           edges (incoming_map, trans_map, trans_input_map, env) *)
        
      in
      (* Compute the labelling as the merge of all inputs *)
      let labelling, env =
        AdjGraph.fold_vertices (fun i (labelling, env) ->
            let init = AdjGraph.VertexMap.find i init_map in
            let in_edges =
              match AdjGraph.VertexMap.Exceptionless.find i incoming_map with
              | None -> []
              | Some es -> es
            in
            let node = avalue (vint i, Some Typing.node_ty, Span.default) in
            let emerge_i = Interp.interp_partial_fun emerge [node] in
            let idx = ref 0 in
            let merged, env =
              (* BatList.fold_right *)
              BatList.fold_left
                (fun (acc, env) (x, y)  ->
                  incr idx ;
                  let trans = AdjGraph.EdgeMap.find (x, y) trans_map in
                  let str = Printf.sprintf "merge-%d-%d" (Integer.to_int i) !idx in
                  let merge_result, x, env = encode_z3_merge str env emerge_i in
                  let env = BatList.fold_left2 (fun env y x ->
                    (* BatList.fold_right2 (fun y x env -> *)
                        add_constraint env (mk_term (mk_eq y.t x.t)))
                                               env (trans @ acc) x
                                               (* (trans @ acc) x env *)
                  in
                  merge_result, env) (init, env) in_edges
                (* merge_result, env) in_edges (init, env) *)
            in
            let lbl_i_name = label_var i in
            let lbl_i = create_strings lbl_i_name aty in
            let lbl_iv = lift1 Var.create lbl_i in
            let env = add_symbolic env lbl_iv aty in
            let l, env = reduce2
                           (fun lbl s (ls, env) ->
                             let l, env = mk_constant env (create_vars env "" lbl) s in
                             (l :: ls, env)) lbl_iv (ty_to_sorts aty) ([], env)
            in
            let env =
              BatList.fold_right2 (fun l merged env ->
                  add_constraint env (mk_term (mk_eq l.t merged.t)))
                                  l merged env
            in
            (AdjGraph.VertexMap.add i l labelling, env))
                               nodes (AdjGraph.VertexMap.empty, env)
      in
      
      (* Propagate labels across edges outputs *)
      let env = AdjGraph.EdgeMap.fold
                  (fun (i, j) x env ->
                    let label = AdjGraph.VertexMap.find i labelling in
                    BatList.fold_left2 (fun env label x ->
                        add_constraint env (mk_term (mk_eq label.t x.t))) env label x)
                    trans_input_map env
                  (*   BatList.fold_right2 (fun label x env -> *)
                  (*       add_constraint env (mk_term (mk_eq label.t x.t))) label x env) *)
                  (* trans_input_map env                     *)
      in
      (* add assertions at the end *)
      let env = 
        match eassert with
        | None -> env
        | Some eassert ->
           let all_good = mk_bool true in
           let all_good, env =
             AdjGraph.fold_vertices
               (fun i (all_good, env) ->
                 let label = AdjGraph.VertexMap.find i labelling in
                 let node = avalue (vint i, Some Typing.node_ty, Span.default) in
                 let eassert_i = Interp.interp_partial_fun eassert [node] in
                 let result, x, env = encode_z3_assert (assert_var i) env i eassert_i in
                 let env =
                   BatList.fold_left2 (fun env x label ->
                       add_constraint env (mk_term (mk_eq x.t label.t)))
                                      env x label
                 in
                 let assertion_holds =
                   BatList.map (fun result -> mk_eq result.t (mk_bool true) |> mk_term) result
               |> of_list |> combine_term in
                 mk_and all_good assertion_holds.t, env
               ) nodes (all_good, env)
           in
           add_constraint env (mk_term (mk_not all_good))
      in
      (* add the symbolic variable constraints *)
      add_symbolic_constraints env (get_requires_no_failures ds) (env.symbolics (*@ sym_vars*))
  end

(* (\** * Alternative SMT encoding *\) *)
(* module FunctionalEncoding (E: ExprEncoding) : Encoding = *)
(*   struct *)
(*     open E *)

(*     let add_symbolic_constraints env requires sym_vars = *)
(*       (\* Declare the symbolic variables: ignore the expression in case of SMT *\) *)
(*       VarMap.iter *)
(*         (fun v e -> *)
(*           let names = create_vars env "" v in *)
(*           mk_constant env names (ty_to_sort (Syntax.get_ty_from_tyexp e)) *)
(*                       ~cdescr:"Symbolic variable decl" *)
(*           |> ignore ) sym_vars ; *)
(*       (\* add the require clauses *\) *)
(*       List.iter *)
(*         (fun e -> *)
(*           let es = encode_exp_z3 "" env e in *)
(*           ignore (lift1 (fun e -> add_constraint env e) es)) requires *)
      
(*  let encode_z3_assert str env node assertion = *)
(*       let rec loop assertion acc = *)
(*         match assertion.e with *)
(*         | EFun {arg= x; argty= Some xty; body= exp} -> *)
(*          (match exp.e with *)
(*           | EFun _ -> *)
(*              loop exp ((x,xty) :: acc) *)
(*           | _ -> *)
(*              let acc = List.rev acc in *)
(*              let xs = List.map (fun (x,xty) -> create_vars env str x) acc in *)
(*              let xstr = List.map (fun x -> mk_constant env x (ty_to_sort xty) *)
(*                                     ~cdescr:"assert x argument" ~cloc:assertion.espan ) xs *)
(*              in *)
(*              let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in *)
(*              let results = *)
(*                lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in      *)
(*              let es = encode_exp_z3 str env exp in *)
(*              ignore(lift2 (fun e result -> *)
(*                         add_constraint env (mk_term (mk_eq result.t e.t))) es results); *)
(*              (results, xstr)) *)
(*         | _ -> failwith "internal error" *)
(*       in *)
(*       loop assertion [] *)
      
(*     let node_exp (u: Integer.t) : Syntax.exp = *)
(*       aexp(e_val (vint u), Some Typing.node_ty, Span.default) *)

(*     let edge_exp (u: Integer.t) (v: Integer.t) : Syntax.exp = *)
(*       aexp(e_val (vtuple [vint u; vint v]), *)
(*            Some Typing.edge_ty, Span.default) *)
      
(*     (\** An alternative SMT encoding, where we build an NV expression for *)
(*    each label, partially evaluate it and then encode it *\) *)
(*     let encode_z3 (ds: declarations) sym_vars : smt_env = *)
(*       let env = init_solver ds in *)
(*       let eassert = get_assert ds in *)
(*       let emerge, etrans, einit, nodes, edges, aty = *)
(*         match *)
(*           ( get_merge ds *)
(*           , get_trans ds *)
(*           , get_init ds *)
(*           , get_nodes ds *)
(*           , get_edges ds *)
(*           , get_attr_type ds ) *)
(*         with *)
(*         | Some emerge, Some etrans, Some einit, Some n, Some es, Some aty -> *)
(*            (emerge, etrans, einit, n, es, aty) *)
(*         | _ -> *)
(*            Console.error *)
(*              "missing definition of nodes, edges, merge, trans or init" *)
(*       in *)
(*       (\* Create a map from nodes to smt variables denoting the label of the node*\) *)
(*       let labelling = *)
(*         AdjGraph.fold_vertices (fun u acc -> *)
(*             let lbl_u_name = label_var u in *)
(*             let lbl_u = create_strings lbl_u_name aty in *)
(*             let lblt = *)
(*               lift2 (mk_constant env) lbl_u (ty_to_sorts aty) in             *)
(*             add_symbolic env (lift1 Var.create lbl_u) aty; *)
(*             AdjGraph.VertexMap.add u lblt acc) *)
(*                                nodes AdjGraph.VertexMap.empty *)
(*       in *)

(*       let init_exp u = eapp einit (node_exp u) in *)
(*       let trans_exp u v x = eapp (eapp etrans (edge_exp u v)) x in *)
(*       let merge_exp u x y = eapp (eapp (eapp emerge (node_exp u)) x) y in *)

(*       (\* map from nodes to incoming messages*\) *)
(*       let incoming_messages_map = *)
(*         List.fold_left (fun acc (u,v) ->  *)
(*             let lblu = aexp (evar (label_var u |> Var.create), Some aty, Span.default) in *)
(*             let transuv = trans_exp u v lblu in *)
(*             AdjGraph.VertexMap.modify_def [] v (fun us -> transuv :: us) acc) *)
(*                        AdjGraph.VertexMap.empty edges *)
(*       in *)

(*       (\* map from nodes to the merged messages *\) *)
(*       let merged_messages_map = *)
(*         AdjGraph.fold_vertices (fun u acc -> *)
(*             let messages = AdjGraph.VertexMap.find_default [] u incoming_messages_map in *)
(*             let best = List.fold_left (fun accm m -> merge_exp u m accm) *)
(*                                       (init_exp u) messages *)
(*             in *)
(*             let str = Printf.sprintf "merge-%d" (Integer.to_int u) in *)
(*             let best_smt = Interp.Full.interp_partial best |> encode_exp_z3 str env in *)
(*             AdjGraph.VertexMap.add u best_smt acc) nodes AdjGraph.VertexMap.empty *)
(*       in *)

(*       AdjGraph.fold_vertices (fun u () -> *)
(*           let lblu = try AdjGraph.VertexMap.find u labelling *)
(*                      with Not_found -> failwith "label variable not found" *)
(*           in *)
(*           let merged = try AdjGraph.VertexMap.find u merged_messages_map *)
(*                        with Not_found -> failwith "merged variable not found" *)
(*           in *)
(*           ignore(lift2 (fun lblu merged -> *)
(*                      add_constraint env (mk_term (mk_eq lblu.t merged.t))) lblu merged)) *)
(*                              nodes (); *)
(*       (\* add assertions at the end *\) *)
(*       (\* TODO: same as other encoding make it a function *\) *)
(*       ( match eassert with *)
(*         | None -> () *)
(*         | Some eassert -> *)
(*            let all_good = ref (mk_bool true) in *)
(*            for i = 0 to Integer.to_int nodes - 1 do *)
(*              let label = *)
(*                AdjGraph.VertexMap.find (Integer.of_int i) labelling *)
(*              in *)
(*              let result, x = *)
(*                encode_z3_assert (assert_var (Integer.of_int i)) env (Integer.of_int i) eassert *)
(*              in *)
(*              List.iter2 (fun x label -> *)
(*                  add_constraint env (mk_term (mk_eq x.t label.t))) x (to_list label); *)
(*              let assertion_holds = *)
(*                lift1 (fun result -> mk_eq result.t (mk_bool true) |> mk_term) result *)
(*                |> combine_term in *)
(*              all_good := *)
(*                mk_and !all_good assertion_holds.t *)
(*            done ; *)
(*            add_constraint env (mk_term (mk_not !all_good))) ; *)
(*       (\* add the symbolic variable constraints *\) *)
(*       add_symbolic_constraints env (get_requires_no_failures ds) (env.symbolics (\*@ sym_vars*\)); *)
(*       env *)
(*   end *)
      
    (** ** SMT query optimization *)
    let rec alpha_rename_smt_term (renaming: string StringMap.t) (tm: smt_term) =
      match tm with
      | Int _ | Bool _ -> tm
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
      | AtMost (tm1, tm2) ->
         AtMost (List.map (alpha_rename_smt_term renaming) tm1,
                 alpha_rename_smt_term renaming tm2)
      | Var s ->
         (match StringMap.Exceptionless.find s renaming with
          | None -> tm
          | Some x -> Var x)
      | App (tm1, tms) ->
         App (alpha_rename_smt_term renaming tm1,
              List.map (alpha_rename_smt_term renaming) tms)
        
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
      let env =
        {env with ctx = BatList.rev_map (fun c ->
                            match c.com with
                            | Assert tm -> {c with com = Assert (alpha_rename_term renaming tm)}
                            | Eval tm -> {c with com = Eval (alpha_rename_term renaming tm)}
                            | _  -> c) new_ctx}
      in
      (* remove unnecessary declarations *)
      (* had to increase stack size to avoid overflow here..
         consider better implementations of this function*)
      let env =
        {env with const_decls =
                    ConstantSet.filter (fun cdecl ->
                        try
                          let repr = StringMap.find cdecl.cname renaming in
                          if repr = cdecl.cname then true else false
                        with Not_found -> true) env.const_decls}
      in
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
          failwith ("failed: " ^ tok)
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
    (*   let buf = Buffer.create 8000000 in *)
    (*   (\* Emit context *\) *)
    (*   Buffer.add_string buf "(set-option :model_evaluator.completion true)\n"; *)
    (*   (\* Emit constant declarations *\) *)
    (*   ConstantSet.iter (fun c -> *)
    (*       Buffer.add_string buf (const_decl_to_smt ~verbose:verbose info c)) env.const_decls; *)
    (*   (\* Emit assertions *\) *)
    (*   BatList.iter (fun c -> Buffer.add_string buf (command_to_smt verbose info c)) env.ctx; *)
    (*   Buffer.add_char buf '\n'; *)
    (*   Buffer.contents buf *)
      
    let env_to_smt ?(verbose=false) info (env : smt_env) =
      let context = BatList.rev_map (fun c -> command_to_smt verbose info c) env.ctx in
      let context = BatString.concat "\n" context in

      (* Emit constants *)
      let constants = ConstantSet.to_list env.const_decls in
      let constants =
        BatString.concat "\n"
                         (BatList.map (fun c -> const_decl_to_smt c)
                                   constants)
      in
      Printf.sprintf "(set-option :model_evaluator.completion true)
                          \n %s\n %s\n" constants context
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
      | false -> failwith "boxed not implemented yet" (*(module Boxed : ExprEncoding)*)

    let solve info query chan ?symbolic_vars ?(params=[]) ds =
      let sym_vars =
        match symbolic_vars with None -> [] | Some ls -> ls
      in
      let module ExprEnc = (val expr_encoding smt_config) in
      let module Enc =
        (val (if smt_config.encoding = Classic then
                (module ClassicEncoding(ExprEnc) : Encoding)
              else
                failwith "functional encoding not implemented yet"))
                (* (module FunctionalEncoding(ExprEnc) : Encoding) *)
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
      ask_solver solver smt_encoding;
      let get_sat reply =
        match reply with
        | UNSAT -> Unsat
        | SAT ->
           (* build a counterexample based on the model provided by Z3 *)
           let num_nodes =
             match get_nodes ds with
             | Some n -> n
             | _ -> failwith "internal error (encode)"
           in
           let eassert = get_assert ds in
           let model = eval_model env.symbolics num_nodes eassert renaming in
           let model_question = commands_to_smt smt_config.verbose info model in
           if query then
             printQuery chan model_question;
           ask_solver solver model_question;
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
        | UNKNOWN ->
           Unknown
        | _ -> failwith "unexpected answer from solver\n"
      in
      match smt_config.failures with
      | None ->
         let q = check_sat info in
         if query then
           printQuery chan q;
         ask_solver solver q;
         let reply = solver |> parse_reply in
         get_sat reply
      | Some k ->
         let rec loop i =
           match (get_requires_failures ds).e with
           | EOp(AtMost n, [e1;_]) ->
              let arg2 = aexp (e_val (vint (Integer.of_int i)), Some (TInt 32), Span.default) in
              let new_req = aexp (eop (AtMost n) [e1; arg2], Some TBool, Span.default) in
              let zes, env = ExprEnc.encode_exp_z3 "" env new_req in
              let zes_smt =
                ExprEnc.(to_list (lift1 (fun ze -> mk_assert ze |> mk_command) zes))
              in
              let q =
                ((Push |> mk_command) :: (zes_smt @ [CheckSat |> mk_command])) |>
                  commands_to_smt smt_config.verbose info
              in
              if query then
                printQuery chan q;
              (* Printf.printf "printed the query\n"; *)
              ask_solver solver q;
              let reply = solver |> parse_reply in
              (* check satisfiability and get model if required *)
              let isSat = get_sat reply in
              (* pop current context *)
              let pop =
                Printf.sprintf "%s\n" ((Pop |> mk_command) |>
                                         command_to_smt smt_config.verbose info)
              in
              if query then
                printQuery chan pop;
              ask_solver solver pop;
              (match isSat with
              | Unsat ->
                 if i = k then Unsat
                 else
                   loop k
              | Sat m -> Sat m
              | Unknown -> Unknown)
           | _ -> failwith "expected failure clause of the form AtMost n"
         in
         loop k
           
