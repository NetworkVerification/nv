open Collections
open SolverUtil

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

(** ** Utility functions for extracting variables from terms *)
(* Retrieve the names of all smt variables which appear in tm *)
let rec get_vars (tm : smt_term) : string list =
  (* This could be optimized to not use @ and be tail-reursive, but I don't
     think our terms are ever very large so it probably doesn't matter *)
  match tm with
  | Int _
  | Bool _
  | Bv _
  | Constructor _ ->
    []
  | Var s ->
    [s]
  | Not tm1 ->
    get_vars tm1
  | And (tm1, tm2)
  | Or (tm1, tm2)
  | Add (tm1, tm2)
  | Sub (tm1, tm2)
  | Eq (tm1, tm2)
  | Lt (tm1, tm2)
  | Leq (tm1, tm2) ->
    get_vars tm1 @ get_vars tm2
  | Ite (tm1, tm2, tm3) ->
    get_vars tm1 @ get_vars tm2 @ get_vars tm3
  | AtMost (tms1, tms2, tm1) ->
    get_vars tm1 @ (List.concat @@ List.map get_vars tms1) @ (List.concat @@ List.map get_vars tms2)
  | App (tm1, tms) ->
    get_vars tm1 @ (List.concat @@ List.map get_vars tms)
;;

let get_vars_in_command com =
  match com.com with
  | Assert tm -> get_vars tm.t
  | _ -> []
;;

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

(*
  We need to name out assertions so they can appear in an unsat core.
  Our naming scheme is as follows:
  They begin with a prefix constraint-#$, where # ensures all names are unique.
  Then they simply contain the names of all the variables which appear in
  the term, separated with $ characters.
*)
let assert_tm_to_name count tm =
  let base = "constraint-" ^ string_of_int count in
  List.fold_left (fun s1 s2 -> s1 ^ "$" ^ s2) base (get_vars tm.t)
;;

let smt_command_to_smt ?(name_asserts=false) ?(count=0) (info : Console.info) (comm : smt_command): string =
  match comm with
  | Echo s ->
    Printf.sprintf "(echo %s)" s
  | Eval tm ->
    Printf.sprintf "(eval %s)" (term_to_smt false info tm)
  | Assert tm ->
    if name_asserts then
      Printf.sprintf "(assert (! %s :named %s))" (term_to_smt false info tm) (assert_tm_to_name count tm)
    else
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
  | Some r -> print_endline r; parse_reply solver

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
