(** * SMT encoding of network *)

open Collections
open Unsigned
open Syntax
open Solution
open SmtUtil

(* TODO: 
   * make everything an smt_command. i.e. assert, declarations, etc.?
   * Make smt_term wrap around terms, print out more helpful
   comments, include location of ocaml source file
   * Have verbosity levels, we don't always need comments everywhere.*)
   
let printList (printer: 'a -> string) (ls: 'a list) (first : string)
              (sep : string) (last : string) =
  let rec loop ls =
    match ls with
    | [] -> ""
    | [l] -> printer l
    | l :: ls -> (printer l) ^ sep ^ (loop ls)
  in
  first ^ (loop ls) ^ last

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
      | ArraySort of sort * sort
      | DataTypeSort of string * (sort list)
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
      | ArraySort (s1, s2) ->
         Printf.sprintf "(Array %s %s)" (sort_to_smt s1) (sort_to_smt s2)
      | DataTypeSort (name, ls) ->
         let args = printList sort_to_smt ls "" " " "" in
         Printf.sprintf "(%s %s)" name args
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
      | Constructor (name, sort) -> name
      | App (Constructor (name, sort), ts) when ts = [] ->
         Printf.sprintf "(as %s %s)" name (sort_to_smt sort) 
      | App (t, ts) ->
         let args = printList smt_term_to_smt ts "" " " "" in 
         Printf.sprintf "(%s %s)" (smt_term_to_smt t) args

    let term_to_smt verbose info (tm : term) =
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
         Printf.sprintf "(check-sat)"
      | GetModel ->
         Printf.sprintf "(get-model)"

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
      | Some r -> OTHER r

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
  
type smt_env =
  { mutable ctx: command list
  ; mutable const_decls: constant BatSet.t (** named constant and its sort *)
  ; mutable type_decls: (string, datatype_decl) BatMap.t
  ; symbolics: (Var.t * ty_or_exp) list }
  
let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n =
  if descr = "" then Var.to_string n
  else Printf.sprintf "%s-%s" descr (Var.to_string n)

(** * Returns the SMT name of a datatype *)
let rec datatype_name (ty : ty) : string =
  match ty with
  | TVar {contents= Link t} -> datatype_name t
  | TTuple ts -> (
    match ts with
    | [] -> failwith "empty tuple"
    | [t] -> datatype_name t
    | ts ->
       let len = List.length ts in
       Printf.sprintf "Pair%d" len)
  | TOption ty -> "Option"
  | _ -> failwith "should be only called on datatypes"

(** Returns the SMT name of any type *)
let rec type_name (ty : ty) : string =
  match ty with
  | TVar {contents= Link t} -> datatype_name t
  | TTuple ts -> (
    match ts with
    | [] -> failwith "empty tuple"
    | [t] -> datatype_name t
    | ts ->
       let len = List.length ts in
       Printf.sprintf "Pair%d" len)
  | TOption ty -> "Option"
  | TBool -> "Bool"
  | TInt _ -> "Int"
  | TMap _ -> failwith "no maps yet"
  | TArrow _ | TVar _ | QVar _ -> failwith "unsupported type in SMT"

(** Translates a [Syntax.ty] to an SMT sort *)
let rec ty_to_sort (ty: ty) : sort =
  match ty with
  | TVar {contents= Link t} -> ty_to_sort t
  | TBool -> BoolSort
  | TInt _ -> IntSort
  | TTuple ts -> (
    match ts with
    | [] -> failwith "empty tuple"
    | [t] -> ty_to_sort t
    | ts ->
       let name = datatype_name ty in
       DataTypeSort (name, List.map ty_to_sort ts))
  | TOption ty' ->
     let name = datatype_name ty in
     DataTypeSort (name, [ty_to_sort ty'])
  | TMap _ -> failwith "unimplemented"
  (*       mk_array_sort ctx (ty_to_sort ctx ty1) (ty_to_sort ctx ty2)*)
  | TVar _ | QVar _ | TArrow _ ->
      failwith
        (Printf.sprintf "internal error (ty_to_sort): %s"
           (Printing.ty_to_string ty))

let mk_array_sort sort1 sort2 = ArraySort (sort1, sort2)

(** Translates a [Syntax.ty] to an SMT datatype declaration *)
let rec ty_to_type_decl (ty: ty) : datatype_decl =
  match ty with
  | TVar {contents= Link t} -> ty_to_type_decl t
  | TInt _ | TBool -> failwith "not a datatype"
  | TOption _ ->
     let name = datatype_name ty in
     let param = VarSort "T1" in
     let none = { constr_name = "mkNone"; constr_args = [] } in
     let some = { constr_name = "mkSome"; constr_args = [("getSome", param)]} in
     { name = name; params = [param]; constructors = [none; some]}        
  | TTuple ts ->
     let len = List.length ts in
     let name = datatype_name ty in
     let params = List.mapi (fun i _ -> VarSort (Printf.sprintf "T%d" i)) ts in
     let mkpair = { constr_name = Printf.sprintf "mkPair%d" len;
                    constr_args =
                      List.mapi (fun i _ ->
                          Printf.sprintf "proj%d" i, List.nth params i) ts} in
     { name = name; params = params; constructors = [mkpair] }
  | TVar _ | QVar _ | TArrow _ | TMap _ ->
     failwith "not a datatype"

(** Finds the declaration for the datatype of ty if it exists,
   otherwise it creates it and adds it to the env *)
let compute_decl (env : smt_env) ty =
  let name = datatype_name ty in
  match BatMap.Exceptionless.find name env.type_decls  with
  | None ->
     let decl = ty_to_type_decl ty in
     env.type_decls <- BatMap.add name decl env.type_decls;
     decl
  | Some decl -> decl

let add_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  env.const_decls <- BatSet.add {cname; csort; cdescr; cloc} env.const_decls

let mk_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  add_constant env ~cdescr:cdescr ~cloc:cloc cname csort;
  (mk_var cname) |> (mk_term ~tdescr:cdescr ~tloc:cloc)

let add_constraint (env : smt_env) (c : term) =
  env.ctx <- (mk_assert c |> mk_command) :: env.ctx
               
(* let mk_array ctx sort value = Z3Array.mk_const_array ctx sort value *)

(* type array_info = *)
(*   { f: Sort.sort -> Sort.sort *)
(*   ; make: Expr.expr -> Expr.expr *)
(*   ; lift: bool } *)

let is_symbolic syms x =
  List.exists (fun (y, e) -> Var.equals x y) syms

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
        let ze = List.hd es |> encode_exp_z3 descr env in
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
    | MCreate, _ | MGet, _
    | MSet, _
    | MMap, _
    | MMapFilter, _ 
    | MMerge, _
    | _ -> failwith "internal error (encode_exp_z3)" )
  | EIf (e1, e2, e3) ->
      let ze1 = encode_exp_z3 descr env e1 in
      let ze2 = encode_exp_z3 descr env e2 in
      let ze3 = encode_exp_z3 descr env e3 in
      mk_ite ze1.t ze2.t ze3.t |>
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
         let pair_decl = compute_decl env ty in
         let pair_sort = ty_to_sort ty in
         let zes = List.map (fun e -> (encode_exp_z3 descr env e).t) es in
         let f = get_constructors pair_decl |> List.hd in
         mk_app (mk_constructor f.constr_name pair_sort) zes |>
           mk_term ~tloc:e.espan
      | _ -> failwith "internal error (encode_exp_z3)" )
  | ESome e1 ->
     let ty = oget e.ety in
     let decl = compute_decl env ty in
     let sort = ty_to_sort ty in
     let f = List.nth (get_constructors decl) 1 in
     let ze = encode_exp_z3 descr env e1 in
     mk_app (mk_constructor f.constr_name sort) [ze.t] |>
       mk_term ~tloc:e.espan
  | EMatch (e, bs) ->
      let name = create_fresh descr "match" in
      let za = mk_constant env name (ty_to_sort (oget e.ety))
                           ~cdescr:(descr ^ "-match") ~cloc:e.espan in
      let ze1 = encode_exp_z3 descr env e in
      add_constraint env (mk_term ~tloc:e.espan (mk_eq za.t ze1.t));
      encode_branches_z3 descr env za bs (oget e.ety)
  | ETy (e, ty) -> encode_exp_z3 descr env e
  | EFun _ | EApp _ -> failwith "function in smt encoding"

(* and make_map env descr arr x (e1, ty1) e2 = *)
(*   let keysort = *)
(*     match get_inner_type (oget e2.ety) with *)
(*     | TMap (ty, _) -> ty_to_sort env.ctx ty *)
(*     | _ -> failwith "internal error (encode_exp_z3)" *)
(*   in *)
(*   let arr2 = *)
(*     { f= (fun s -> mk_array_sort env.ctx keysort (arr.f s)) *)
(*     ; make= (fun e -> mk_array env.ctx keysort (arr.make e)) *)
(*     ; lift= true } *)
(*   in *)
(*   let e1 = encode_exp_z3 descr env arr2 e1 in *)
(*   let e2 = encode_exp_z3 descr env arr e2 in *)
(*   let x = create_name descr x in *)
(*   let xty = ty_to_sort env.ctx (oget ty1) |> arr2.f in *)
(*   let xarg = Expr.mk_const_s env.ctx x xty in *)
(*   Solver.add env.solver [Boolean.mk_eq env.ctx xarg e2] ; *)
(*   (e1, xarg) *)

(* and encode_op_z3 descr env f arr es = *)
(*   match es with *)
(*   | [] -> failwith "internal error (encode_op)" *)
(*   | [e] -> encode_exp_z3 descr env arr e *)
(*   | e :: es -> *)
(*       let ze1 = encode_exp_z3 descr env arr e in *)
(*       let ze2 = encode_op_z3 descr env f arr es in *)
(*       f ze1 ze2 *)

and encode_branches_z3 descr env name bs (t: ty) =
  match List.rev bs with
  | [] -> failwith "internal error (encode_branches)"
  | (p, e) :: bs ->
      let ze = encode_exp_z3 descr env e in
      (* we make the last branch fire no matter what *)
      let _ = encode_pattern_z3 descr env name p t in
      encode_branches_aux_z3 descr env name (List.rev bs) ze t

(* I'm assuming here that the cases are exhaustive *)
and encode_branches_aux_z3 descr env name bs accze (t: ty) =
  match bs with
  | [] -> accze
  | (p, e) :: bs ->
      let ze = encode_exp_z3 descr env e in
      let zp = encode_pattern_z3 descr env name p t in
      let ze = mk_ite zp.t ze.t accze.t |> mk_term in
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
        let znames =
          List.mapi
            (fun i t ->
              let sort = ty_to_sort t in
              ( mk_constant env (Printf.sprintf "elem%d" i |> create_fresh descr) sort
              , sort
              , t ) )
            ts
        in
        let tup_decl = compute_decl env ty in
        let fs = tup_decl |> get_constructors |> List.hd |> get_projections in
        List.combine znames fs
        |> List.iter (fun ((elem, _, _), (f, _)) ->
               let e = mk_term (mk_app (mk_var f) [zname.t]) in
               add_constraint env ((mk_eq elem.t e.t) |> mk_term));
        let matches =
          List.map
            (fun (p, (zname, _, ty)) ->
              encode_pattern_z3 descr env zname p ty )
            (List.combine ps znames)
        in
        let f acc e = mk_and acc e.t in
        let b = mk_bool true in
        let base = b in
        (List.fold_left f base matches) |>
          mk_term)
  | POption None, TOption _ ->
     let opt_decl = compute_decl env ty in
      let f = opt_decl |> get_constructors |> List.hd |> get_recognizer in
      mk_app (mk_var f) [zname.t] |>
        mk_term
  | POption (Some p), TOption t ->
      let new_name = create_fresh descr "option" in
      let za = mk_constant env new_name (ty_to_sort t) in
      let opt_decl = compute_decl env ty in
      let some_cons = List.nth (opt_decl |> get_constructors) 1 in
      let get_some, _ = some_cons |> get_projections |> List.hd in
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
        let zes = List.map (fun v -> (encode_value_z3 descr env v).t) vs in
        let f = (pair_decl |> get_constructors |> List.hd).constr_name in
        mk_app (mk_constructor f (ty_to_sort (oget v.vty))) zes |>
          mk_term ~tloc:v.vspan
    | _ -> failwith "internal error (encode_value)" )
  | VOption None ->
     let opt_decl = compute_decl env (oget v.vty) in
     let f = (opt_decl |> get_constructors |> List.hd).constr_name in
     let e = mk_app (mk_constructor f (ty_to_sort (oget v.vty))) [] in
     mk_term ~tloc:v.vspan e
  | VOption (Some v1) ->
     let opt_decl = compute_decl env (oget v.vty) in
     let f = (List.nth (opt_decl |> get_constructors) 1).constr_name in
     let zv = encode_value_z3 descr env v1 in
     mk_app (mk_constructor f (ty_to_sort (oget v.vty))) [zv.t] |>
       mk_term ~tloc:v.vspan
  | VClosure _ -> failwith "internal error (closure in smt)"
  | VMap map -> failwith "not doing maps yet"

let exp_to_z3 = encode_exp_z3
              
let encode_z3_merge str env e =
  match e.e with
  | EFun { arg= x
         ; argty= xty
         ; body= {e= EFun {arg= y; argty= yty; body= exp} }} ->
     let xstr =
       mk_constant env (create_name str x) (ty_to_sort (oget xty))
                   ~cdescr:"merge x argument" ~cloc:e.espan
     in
     let ystr =
       mk_constant env (create_name str y) (ty_to_sort (oget yty))
                   ~cdescr:"merge y argument" ~cloc:e.espan
     in
     let name = Printf.sprintf "%s-result" str in
     let result = mk_constant env name (oget exp.ety |> ty_to_sort) in
     let e = encode_exp_z3 str env exp in
     add_constraint env (mk_term (mk_eq result.t e.t));
     (result, xstr, ystr)
  | _ -> failwith "internal error (encode_z3_merge)"

let encode_z3_trans str env edge trans =
  let edge = avalue (vtuple [vint (fst edge); vint (snd edge)],
                     Some Typing.edge_ty, Span.default) in
  let etrans_uv = Interp.interp_partial_fun trans [edge] in
  match etrans_uv.e with
  | EFun {arg= x; argty= xty; body= exp} ->
     (* let edgestr = mk_constant env (create_name str edgevar)
        (ty_to_s    ort (oget edgety)) in *) 
     let xstr = mk_constant env (create_name str x) (ty_to_sort  (oget xty))      
     in
     let name = Printf.sprintf "%s-result" str in
     let result =
       mk_constant env name (oget exp.ety |> ty_to_sort) in
     let e = encode_exp_z3 str env exp in
     add_constraint env (mk_term (mk_eq result.t e.t));
     (result, xstr)
  | _ -> failwith "internal error"

let encode_z3_init str env i e =
  match e.e with
  | EFun {arg= node; argty= nodety; body= _} ->
     let einit_i = Interp.interp_partial_fun e [vint i] in
     (* let nodestr = mk_constant env (create_name str node) (ty_to_sort (oget nodety)) in *)
     let name = Printf.sprintf "%s-result" str in
     let result = mk_constant env name (oget einit_i.ety |> ty_to_sort) in
     let e = encode_exp_z3 str env einit_i in
     add_constraint env (mk_term (mk_eq result.t e.t));
     result
  | _ -> failwith "internal error"

let encode_z3_assert str env node assertion =
  let node = avalue (vint node, Some Typing.node_ty, Span.default) in
  let eassert_u = Interp.interp_partial_fun assertion [node] in
  match eassert_u.e with
  | EFun {arg= x; argty= xty; body= exp} ->
     let xstr = mk_constant env (create_name str x) (ty_to_sort (oget xty)) in     
     let name = Printf.sprintf "%s-result" str in
     let result =
       mk_constant env name (oget exp.ety |> ty_to_sort) in
     let e = encode_exp_z3 str env exp in
     add_constraint env (mk_term (mk_eq result.t e.t));
     (result, xstr)
  | _ -> failwith "internal error"


(** ** Naming convention of useful variables *)
let label_var i =
  Printf.sprintf "label-%d" (Integer.to_int i)

let node_of_label_var s =
  Integer.of_string (BatString.lchop ~n:6 s)
  
let assert_var i =
  Printf.sprintf "assert-%d" (Integer.to_int i)

  (* this is flaky, the variable name used by SMT will be
     assert-n-result, we need to chop both ends *)
let node_of_assert_var s =
  Integer.of_string (BatString.lchop ~n:7 s |> BatString.rchop ~n:7)

let symbolic_var (s: Var.t) =
  Var.to_string s
        
let add_symbolic_constraints env requires sym_vars =
  (* Declare the symbolic variables: ignore the expression in case of SMT *)
  List.iter
    (fun (v, e) ->
      let _ = mk_constant env (symbolic_var v) (ty_to_sort (Syntax.get_ty_from_tyexp e))
                          ~cdescr:"Symbolic variable decl" in ()) sym_vars ;
  (* add the require clauses *)
  List.iter
    (fun e ->
      let e = encode_exp_z3 "" env e in
      add_constraint env e) requires

let init_solver ds =
  Var.reset () ;
  let symbolics = get_symbolics ds in
  { ctx = [];
    const_decls = BatSet.empty;
    type_decls = BatMap.empty;
    symbolics = symbolics }

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
  let init_map = ref Graph.VertexMap.empty in
  for i = 0 to Integer.to_int nodes - 1 do
    let init =
      encode_z3_init (Printf.sprintf "init-%d" i) env (Integer.of_int i) einit
    in
    (* add_constraint env (mk_term (mk_eq n.t (mk_int i))); *)
    init_map := Graph.VertexMap.add (Integer.of_int i) init !init_map
  done ;
  
  (* Map each edge to transfer function result *)
  
  (* incoming_map is a map from vertices to list of incoming edges *)
  let incoming_map = ref Graph.VertexMap.empty in
  (* trans_map maps each edge to the variable that holds the result *)
  let trans_map = ref Graph.EdgeMap.empty in
  (* trans_input_map maps each edge to the incoming message variable *)
  let trans_input_map = ref Graph.EdgeMap.empty in
  List.iter
    (fun (i, j) ->
      ( try
          let idxs = Graph.VertexMap.find j !incoming_map in
          incoming_map :=
            Graph.VertexMap.add j ((i, j) :: idxs) !incoming_map
        with _ ->
          incoming_map :=
            Graph.VertexMap.add j [(i, j)] !incoming_map ) ;
      let trans, x =
        encode_z3_trans
          (Printf.sprintf "trans-%d-%d" (Integer.to_int i)
                          (Integer.to_int j)) 
          env (i, j) etrans
      in
      trans_input_map := Graph.EdgeMap.add (i, j) x !trans_input_map ;
      trans_map := Graph.EdgeMap.add (i, j) trans !trans_map )
    edges ;
  
  (* Compute the labelling as the merge of all inputs *)
  let labelling = ref Graph.VertexMap.empty in
  for i = 0 to Integer.to_int nodes - 1 do
    let init = Graph.VertexMap.find (Integer.of_int i) !init_map in
    let in_edges =
      try Graph.VertexMap.find (Integer.of_int i) !incoming_map
      with Not_found -> []
    in
    let node = avalue (vint (Integer.of_int i), Some Typing.node_ty, Span.default) in
    let emerge_i = Interp.interp_partial_fun emerge [node] in
    let idx = ref 0 in
    let merged =
      List.fold_left
        (fun acc (x, y) ->
          incr idx ;
          let trans = Graph.EdgeMap.find (x, y) !trans_map in
          let str = Printf.sprintf "merge-%d-%d" i !idx in
          let merge_result, x, y =
            encode_z3_merge str env emerge_i
          in
          add_constraint env (mk_term (mk_eq trans.t x.t));
          add_constraint env (mk_term (mk_eq acc.t y.t));
          merge_result )
        init in_edges
    in
    let l = mk_constant env (label_var (Integer.of_int i)) (ty_to_sort aty) in
    add_constraint env (mk_term (mk_eq l.t merged.t));
    labelling := Graph.VertexMap.add (Integer.of_int i) l !labelling
  done ;
  (* Propagate labels across edges outputs *)
  Graph.EdgeMap.iter
    (fun (i, j) x ->
      let label = Graph.VertexMap.find i !labelling in
      add_constraint env (mk_term (mk_eq label.t x.t))) !trans_input_map ;
  (* add assertions at the end *)
  ( match eassert with
  | None -> ()
  | Some eassert ->
      let all_good = ref (mk_bool true) in
      for i = 0 to Integer.to_int nodes - 1 do
        let label =
          Graph.VertexMap.find (Integer.of_int i) !labelling
        in
        let result, x =
          encode_z3_assert (assert_var (Integer.of_int i)) env (Integer.of_int i) eassert
        in
        add_constraint env (mk_term (mk_eq x.t label.t));
        (* add_constraint env (mk_term (mk_eq n.t (mk_int i))); *)
        let assertion_holds = mk_eq result.t (mk_bool true) in
        all_good :=
          mk_and !all_good assertion_holds
      done ;
      add_constraint env (mk_term (mk_not !all_good))) ;
  (* add the symbolic variable constraints *)
  add_symbolic_constraints env (get_requires ds) (env.symbolics (*@ sym_vars*));
  env

type smt_result = Unsat | Unknown | Sat of Solution.t

(** Emits the code that evaluates the model returned by Z3. *)  
let eval_model (symbolics: (Var.t * Syntax.ty_or_exp) list)
      (num_nodes: Integer.t)
      (eassert: Syntax.exp option) : command list =
  let var x = "Var:" ^ x in
  (* Compute eval statements for labels *)
  let labels =
    Graph.fold_vertices (fun u acc ->
        let tm = mk_var (label_var u) |> mk_term in
        let ev = mk_eval tm |> mk_command in
        let ec = mk_echo ("\"" ^ (var (label_var u)) ^ "\"") |> mk_command in
        ec :: ev :: acc) num_nodes [(mk_echo ("\"end_of_model\"") |> mk_command)] in
  (* Compute eval statements for assertions *)
  let assertions =
    match eassert with
    | None -> labels
    | Some _ ->
       Graph.fold_vertices (fun u acc ->
           let tm = mk_var ((assert_var u) ^ "-result") |> mk_term in
           let ev = mk_eval tm |> mk_command in
           let ec = mk_echo ("\"" ^ (var ((assert_var u) ^ "-result")) ^ "\"")
                             |> mk_command in
           ec :: ev :: acc) num_nodes labels
  in
  (* Compute eval statements for symbolic variables *)
  let symbols =
    List.fold_left (fun acc (sv, _) ->
        let tm = mk_var (symbolic_var sv) |> mk_term in
        let ev = mk_eval tm |> mk_command in
        let ec = mk_echo ("\"" ^ (var (symbolic_var sv)) ^ "\"") |> mk_command in
        ec :: ev :: acc) assertions symbolics in
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
         {sol with labels= Graph.VertexMap.add (node_of_label_var k) nvval sol.labels}
      | k when BatString.starts_with k "assert-" ->
         {sol with assertions=
                     match sol.assertions with
                     | None ->
                        Some (Graph.VertexMap.add (node_of_assert_var k)
                                                  (nvval |> Syntax.bool_of_val |> oget)
                                                  Graph.VertexMap.empty)
                     | Some m ->
                        Some (Graph.VertexMap.add (node_of_assert_var k)
                                                  (nvval |> Syntax.bool_of_val |> oget) m)
         }
      | k ->
         {sol with symbolics= Collections.StringMap.add k nvval sol.symbolics}) m
               {symbolics = StringMap.empty;
                labels = Graph.VertexMap.empty;
                assertions= None}
  
(** ** Translate the environment to SMT-LIB2 *)
  
let env_to_smt ?(verbose=false) info (env : smt_env) =
  (* Emit context *)
  let context = List.rev_map (fun c -> command_to_smt verbose info c) env.ctx in
  let context = String.concat "\n" context in

  (* Emit constants *)
  let constants = BatSet.to_list env.const_decls in
  let constants =
    String.concat "\n"
                  (List.map (fun c -> const_decl_to_smt ~verbose:verbose info c) constants) in
  (* Emit type declarations *)
  let decls = BatMap.bindings env.type_decls in
  let decls = String.concat "\n"
            (List.map (fun (_,typ) -> type_decl_to_smt typ) decls) in
  Printf.sprintf "%s\n" (decls ^ constants ^ context)
(* this new line is super important otherwise we don't get a reply
   from Z3.. not understanding why*)

let check_sat (env: smt_env) =
  env.ctx <- (CheckSat |> mk_command) :: env.ctx

let time_profile msg (f: unit -> 'a) : 'a =
  let start_time = Sys.time () in
  let res = f () in
  let finish_time = Sys.time () in
  Printf.printf "%s took: %f secs to complete\n%!" msg (finish_time -. start_time);
  res

let printQuery (chan: out_channel Lazy.t) (msg: string) =
  let chan = Lazy.force chan in
  Printf.fprintf chan "%s" msg; flush chan
  
let solve info query chan ?symbolic_vars ?(params=[]) ds =
  let sym_vars =
    match symbolic_vars with None -> [] | Some ls -> ls
  in
  let verbose = false in

  (* compute the encoding of the network *)
  let env = time_profile "Encoding network" (fun () -> encode_z3 ds sym_vars) in
  (* let env = encode_z3 ds sym_vars in *)
  check_sat env;
  let smt_encoding = time_profile "Compiling query"
                                  (fun () -> env_to_smt ~verbose:verbose info env) in
  (* let smt_encoding =  env_to_smt ~verbose:verbose env in *)
  if query then
    printQuery chan smt_encoding;
  (* start communication with solver process *)
  let solver = start_solver params in
  ask_solver solver smt_encoding;
  let reply = solver |> parse_reply in
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
     let model = eval_model env.symbolics num_nodes eassert in
     let model_question = commands_to_smt verbose info model in
     printQuery chan model_question;
     ask_solver solver model_question;
     let model = solver |> parse_model in
     (match model with
      | MODEL m -> Sat (translate_model m)
      | OTHER s ->
         Printf.printf "%s\n" s;
         failwith "failed to parse a model"
      | _ -> failwith "failed to parse a model")
  | UNKNOWN ->
     Unknown
  | _ -> failwith "unexpected answer from solver\n"
  
  
