open Nv_datastructures
open Nv_lang
open Collections
open SolverUtil

(* ** SMT configuration*)
(* Classic encodes the SRP as an SMT expression, Functional encodes
   the problem as an NV term which is then translated to SMT *)
type encoding_style =
  | Classic
  | Functional

type smt_options =
  { mutable verbose : bool
  ; mutable optimize : bool
  ; mutable encoding : encoding_style
  ; mutable unboxing : bool
  ; mutable parallel : bool
  ; mutable failures : int option
  ; mutable infinite_arith : bool
  ; mutable multiplicities : int StringMap.t
  }

let smt_config : smt_options =
  { verbose = false
  ; optimize = true
  ; encoding = Classic
  ; unboxing = false
  ; parallel = false
  ; failures = None
  ; infinite_arith = true
  ; multiplicities = StringMap.empty
  }
;;

let get_requires_no_failures req =
  let open Nv_lang.Syntax in
  BatList.filter
    (fun e ->
      match e.e with
      | EOp (AtMost _, _) -> false
      | _ -> true)
    req
;;

let get_requires_failures req =
  let open Nv_lang.Syntax in
  BatList.filter
    (fun e ->
      match e.e with
      | EOp (AtMost _, _) -> true
      | _ -> false)
    req
  |> List.hd
;;

(** * SMT language*)
module SmtLang = struct
  let printVerbose (msg : string) (descr : string) (span : Span.t) info =
    let sl =
      match Console.get_start_position span info with
      | Some (sl, _) -> sl
      | _ -> -1
    in
    let fl =
      match Console.get_end_position span info with
      | Some (fl, _) -> fl
      | _ -> -1
    in
    Printf.sprintf "; %s: %s on %d-%d\n" msg descr sl fl
  ;;

  let printList
      (printer : 'a -> string)
      (ls : 'a list)
      (first : string)
      (sep : string)
      (last : string)
    =
    let buf = Buffer.create 5000 in
    let rec loop ls =
      match ls with
      | [] -> ()
      | [l] -> Buffer.add_string buf (printer l)
      | l :: ls ->
        Buffer.add_string buf (printer l);
        Buffer.add_string buf sep;
        loop ls
    in
    Buffer.add_string buf first;
    loop ls;
    Buffer.add_string buf last;
    Buffer.contents buf
  ;;

  type datatype_decl =
    { name : string
    ; params : sort list
    ; constructors : constructor_decl list
    }

  and constructor_decl =
    { constr_name : string (** name of constructor *)
    ; constr_args : (string * sort) list
          (** projection functions
                                           and their type *)
    }

  and sort =
    | UnitSort
    | BoolSort
    | IntSort
    | MapSort of sort * sort
    | DataTypeSort of string * sort list
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
    | BvAdd of smt_term * smt_term
    | BvSub of smt_term * smt_term
    | BvLt of smt_term * smt_term
    | BvLeq of smt_term * smt_term
    | BvAnd of smt_term * smt_term
    | AtMost of smt_term list * smt_term list * smt_term
    | IntToBv of smt_term * int
    | BvToInt of smt_term * int
    | Constructor of string * sort (** constructor name, instantiated sort*)
    | App of smt_term * smt_term list

  type term =
    { t : smt_term
    ; tdescr : string
    ; tloc : Span.t
    }

  type constant =
    { cname : string
    ; csort : sort
    ; cdescr : string
    ; cloc : Span.t
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
    { com : smt_command
    ; comdescr : string
    ; comloc : Span.t
    }

  (** ** Constructors for SMT terms *)

  let mk_int_u32 i = Int (i |> Integer.to_int |> string_of_int)
  let mk_int i = Int (string_of_int i)
  let mk_bool b = Bool b
  let mk_var s = Var s
  let mk_bv i = Bv i
  let mk_constructor f ts = Constructor (f, ts)
  let mk_app f args = App (f, args)
  let mk_and t1 t2 = And (t1, t2)

  let mk_and_fast t1 t2 =
    match t1, t2 with
    | Bool true, _ -> t2
    | Bool false, _ -> Bool false
    | _, Bool true -> t1
    | _, Bool false -> Bool false
    | _, _ -> mk_and t1 t2
  ;;

  let mk_or t1 t2 = Or (t1, t2)

  let mk_or_fast t1 t2 =
    match t1, t2 with
    | Bool true, _ -> Bool true
    | Bool false, _ -> t2
    | _, Bool true -> Bool true
    | _, Bool false -> t1
    | _, _ -> mk_or t1 t2
  ;;

  let mk_not t1 = Not t1

  let mk_not_fast t1 =
    match t1 with
    | Bool b -> mk_bool (not b)
    | _ -> mk_not t1
  ;;

  let mk_add t1 t2 = Add (t1, t2)
  let mk_sub t1 t2 = Sub (t1, t2)

  let mk_eq t1 t2 =
    match t1, t2 with
    | Bool b1, Bool b2 -> mk_bool (b1 = b2)
    | Int i1, Int i2 -> mk_bool (i1 = i2)
    | _ -> Eq (t1, t2)
  ;;

  let mk_lt t1 t2 = if t2 = Int "0" then Bool false else Lt (t1, t2)
  let mk_leq t1 t2 = Leq (t1, t2)
  let mk_bv_add t1 t2 = BvAdd (t1, t2)
  let mk_bv_sub t1 t2 = BvSub (t1, t2)
  let mk_bv_sub t1 t2 = BvAnd (t1, t2)
  let mk_bv_lt t1 t2 = BvLt (t1, t2)
  let mk_bv_leq t1 t2 = BvLeq (t1, t2)
  let mk_int_to_bv t1 sz = IntToBv (t1, sz)
  let mk_bv_to_int t1 sz = BvToInt (t1, sz)

  (* Bitwise and for bitvectors *)
  let mk_bv_uand t1 t2 = BvAnd (t1, t2)

  (* Bitwise and for integers *)
  let mk_uand t1 t2 sz =
    mk_bv_to_int (mk_bv_uand (mk_int_to_bv t1 sz) (mk_int_to_bv t2 sz)) sz
  ;;

  let mk_ite t1 t2 t3 = Ite (t1, t2, t3)

  let mk_ite_fast t1 t2 t3 =
    match t1 with
    | Bool b -> if b then t2 else t3
    | _ ->
      (match t2, t3 with
      | Bool true, Bool false -> t1
      | Bool false, Bool true -> Not t1
      | Bool true, Bool true -> Bool true
      | Bool false, Bool false -> Bool false
      | Int i1, Int i2 when i1 = i2 -> t2
      | Bv i1, Bv i2 when i1 = i2 -> t2
      (* this did not help at all..*)
      (* | t2, Ite (t1', t2', t3') when t2 = t2' ->
       *   mk_ite (mk_or_fast t1 t1') t2 t3' *)
      | _, _ -> (* if t2 = t3 then t2
                 * else *) mk_ite t1 t2 t3)
  ;;

  let mk_atMost t1 t2 t3 = AtMost (t1, t2, t3)
  let mk_term ?(tdescr = "") ?(tloc = Span.default) (t : smt_term) = { t; tdescr; tloc }

  (** ** Constructors for SMT commands *)

  let mk_echo s = Echo s
  let mk_eval tm = Eval tm
  let mk_assert tm = Assert tm

  let mk_command ?(comdescr = "") ?(comloc = Span.default) (com : smt_command) =
    { com; comdescr; comloc }
  ;;

  (** ** Functions related to datatype constructors *)

  let get_constructors decl = decl.constructors
  let get_projections (constr : constructor_decl) = constr.constr_args
  let get_recognizer (constr : constructor_decl) = "is-" ^ constr.constr_name

  (* Retrieve the names of all smt variables which appear in tm *)

  (** ** Utility functions for extracting variables from terms *)
  let rec get_vars (tm : smt_term) : string list =
    (* This could be optimized to not use @ and be tail-reursive, but I don't
         think our terms are ever very large so it probably doesn't matter *)
    match tm with
    | Int _ | Bool _ | Bv _ | Constructor _ -> []
    | Var s -> [s]
    | Not tm1 | IntToBv (tm1, _) | BvToInt (tm1, _) -> get_vars tm1
    | And (tm1, tm2)
    | Or (tm1, tm2)
    | Add (tm1, tm2)
    | Sub (tm1, tm2)
    | Eq (tm1, tm2)
    | Lt (tm1, tm2)
    | BvAdd (tm1, tm2)
    | BvSub (tm1, tm2)
    | BvLt (tm1, tm2)
    | BvLeq (tm1, tm2)
    | BvAnd (tm1, tm2)
    | Leq (tm1, tm2) -> get_vars tm1 @ get_vars tm2
    | Ite (tm1, tm2, tm3) -> get_vars tm1 @ get_vars tm2 @ get_vars tm3
    | AtMost (tms1, tms2, tm1) ->
      get_vars tm1
      @ (List.concat @@ List.map get_vars tms1)
      @ List.concat
      @@ List.map get_vars tms2
    | App (tm1, tms) -> get_vars tm1 @ List.concat @@ List.map get_vars tms
  ;;

  let get_vars_in_command com =
    match com.com with
    | Assert tm -> get_vars tm.t
    | _ -> []
  ;;

  (** ** Compilation to SMT-LIB2 *)

  let rec sort_to_smt (s : sort) : string =
    match s with
    | UnitSort -> "Unit"
    | BoolSort -> "Bool"
    | IntSort -> "Int"
    | MapSort (s1, s2) -> Printf.sprintf "((%s) %s)" (sort_to_smt s1) (sort_to_smt s2)
    | DataTypeSort (name, ls) ->
      let args = printList sort_to_smt ls "" " " "" in
      Printf.sprintf "(%s %s)" name args
    | BitVecSort n -> Printf.sprintf "(_ BitVec %d)" n
    | VarSort s -> s
  ;;

  let rec smt_term_to_smt (tm : smt_term) : string =
    match tm with
    | Int s -> s
    | Bool b -> if b then "true" else "false"
    | And (b1, b2) ->
      Printf.sprintf "(and %s %s)" (smt_term_to_smt b1) (smt_term_to_smt b2)
    | Or (b1, b2) -> Printf.sprintf "(or %s %s)" (smt_term_to_smt b1) (smt_term_to_smt b2)
    | Not b -> Printf.sprintf "(not %s)" (smt_term_to_smt b)
    | Add (n, m) -> Printf.sprintf "(+ %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
    | Sub (n, m) -> Printf.sprintf "(- %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
    | Eq (n, m) -> Printf.sprintf "(= %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
    | Lt (n, m) -> Printf.sprintf "(< %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
    | Leq (n, m) -> Printf.sprintf "(<= %s %s)" (smt_term_to_smt n) (smt_term_to_smt m)
    | Ite (t1, t2, t3) ->
      Printf.sprintf
        "(ite %s %s %s)"
        (smt_term_to_smt t1)
        (smt_term_to_smt t2)
        (smt_term_to_smt t3)
    | Var s -> s
    | Bv n -> Printf.sprintf "(_ bv%d %d)" (Integer.to_int n) (Integer.size n)
    | BvAdd (t1, t2) ->
      Printf.sprintf "(bvadd %s %s)" (smt_term_to_smt t1) (smt_term_to_smt t2)
    | BvSub (t1, t2) ->
      Printf.sprintf "(bvsub %s %s)" (smt_term_to_smt t1) (smt_term_to_smt t2)
    | BvLt (t1, t2) ->
      Printf.sprintf "(bvult %s %s)" (smt_term_to_smt t1) (smt_term_to_smt t2)
    | BvLeq (t1, t2) ->
      Printf.sprintf "(bvule %s %s)" (smt_term_to_smt t1) (smt_term_to_smt t2)
    | BvAnd (t1, t2) ->
      Printf.sprintf "(bvand %s %s)" (smt_term_to_smt t1) (smt_term_to_smt t2)
    | IntToBv (t1, sz) -> Printf.sprintf "((_ int2bv %d) %s)" sz (smt_term_to_smt t1)
    | BvToInt (t1, sz) -> Printf.sprintf "((_ bv2int %d) %s)" sz (smt_term_to_smt t1)
    | AtMost (ts1, ts2, t1) ->
      Printf.sprintf
        "((_ pble %s %s) %s)"
        (smt_term_to_smt t1)
        (printList (fun x -> smt_term_to_smt x) ts2 "" " " "")
        (printList (fun x -> smt_term_to_smt x) ts1 "" " " "")
    | Constructor (name, _sort) -> name
    | App (Constructor (name, sort), ts) when ts = [] ->
      Printf.sprintf "(as %s %s)" name (sort_to_smt sort)
    | App (t, ts) ->
      let args = printList smt_term_to_smt ts "" " " "" in
      Printf.sprintf "(%s %s)" (smt_term_to_smt t) args
  ;;

  let term_to_smt _verbose _info (tm : term) = smt_term_to_smt tm.t

  let term_to_smt_meta verbose info (tm : term) =
    (if verbose
    then printVerbose "Translating expression:" tm.tdescr tm.tloc info
    else "")
    ^ smt_term_to_smt tm.t
  ;;

  let constructor_to_smt (c : constructor_decl) : string =
    match c.constr_args with
    | [] -> c.constr_name
    | p :: ps ->
      let constrArgs =
        printList
          (fun (p, s) -> Printf.sprintf "(%s %s)" p (sort_to_smt s))
          (p :: ps)
          ""
          " "
          ""
      in
      Printf.sprintf "(%s %s)" c.constr_name constrArgs
  ;;

  let rec type_decl_to_smt (dt : datatype_decl) : string =
    Printf.sprintf
      "(declare-datatypes %s ((%s %s)))"
      (printList sort_to_smt dt.params "(" " " ")")
      dt.name
      (printList constructor_to_smt dt.constructors "" " " "")
  ;;

  let const_decl_to_smt ?(verbose = false) info const : string =
    (if verbose
    then printVerbose "Constant declared about:" const.cdescr const.cloc info
    else "")
    ^ Printf.sprintf "(declare-const %s %s)" const.cname (sort_to_smt const.csort)
  ;;

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

  let smt_command_to_smt
      ?(name_asserts = false)
      ?(count = 0)
      (info : Console.info)
      (comm : smt_command)
      : string
    =
    match comm with
    | Echo s -> Printf.sprintf "(echo %s)" s
    | Eval tm -> Printf.sprintf "(eval %s)" (term_to_smt false info tm)
    | Assert tm ->
      if name_asserts
      then
        Printf.sprintf
          "(assert (! %s :named %s))"
          (term_to_smt false info tm)
          (assert_tm_to_name count tm)
      else Printf.sprintf "(assert %s)" (term_to_smt false info tm)
    | CheckSat ->
      (* for now i am hardcoding the tactics here. *)
      if smt_config.parallel
      then
        Printf.sprintf
          "(set-option :parallel.enable true)\n\
           (check-sat-using (then simplify propagate-values simplify solve-eqs bit-blast \
           psat))\n"
      else if smt_config.infinite_arith
      then
        Printf.sprintf
          "(set-option :smt.arith.nl false)\n\
           (check-sat-using (then simplify propagate-values simplify solve-eqs smt))"
      else
        Printf.sprintf
          "(check-sat-using (then simplify propagate-values simplify solve-eqs bit-blast \
           smtfd))"
    | GetModel -> Printf.sprintf "(get-model)"
    | Push -> Printf.sprintf "(push)"
    | Pop -> Printf.sprintf "(pop)"
  ;;

  (* NOTE: this currently ignores the comment/loc of the term inside
   the command. Perhaps we would like to combine them in some way
           *)

  let command_of_term_meta info (comm : command) : string =
    match comm.com with
    | Eval tm | Assert tm ->
      printVerbose "Translating command:" comm.comdescr comm.comloc info
      ^ printVerbose "Translating command:" tm.tdescr tm.tloc info
    | _ -> printVerbose "Translating command:" comm.comdescr comm.comloc info
  ;;

  let command_to_smt (_verbose : bool) info (com : command) : string =
    smt_command_to_smt info com.com
  ;;

  let command_to_smt_meta (verbose : bool) info (com : command) : string =
    (if verbose then command_of_term_meta info com else "")
    ^ smt_command_to_smt info com.com
  ;;

  let commands_to_smt (verbose : bool) info (coms : command list) : string =
    printList (fun c -> command_to_smt verbose info c) coms "\n" "\n" "\n"
  ;;

  type smt_answer =
    | UNSAT
    | SAT
    | UNKNOWN
    | MODEL of (string, string) BatMap.t
    | OTHER of string
end

(** ** SMT Environment*)
open SmtLang

module Constant = struct
  type t = constant

  let compare x y = compare x.cname y.cname
end

module ConstantSet = BatSet.Make (Constant)

type smt_env =
  { mutable ctx : command list
  ; mutable const_decls : ConstantSet.t (** named constant and its sort *)
  ; mutable type_decls : datatype_decl StringMap.t
  ; mutable symbolics : Nv_lang.Syntax.ty_or_exp VarMap.t
  }

let create_fresh descr s = Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n =
  if descr = "" then Var.to_string n else Printf.sprintf "%s-%s" descr (Var.to_string n)
;;

(** * Returns the SMT name of a datatype *)
let rec datatype_name (ty : Nv_lang.Syntax.ty) : string option =
  let open Nv_lang.Syntax in
  match ty with
  | TVar { contents = Link t } -> datatype_name t
  | TTuple ts ->
    (match ts with
    | [t] -> datatype_name t
    | ts ->
      let len = BatList.length ts in
      Some (Printf.sprintf "Pair%d" len))
  | TOption _ty -> Some "Option"
  | _ -> None
;;

let add_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  env.const_decls <- ConstantSet.add { cname; csort; cdescr; cloc } env.const_decls
;;

let mk_constant (env : smt_env) ?(cdescr = "") ?(cloc = Span.default) cname csort =
  add_constant env ~cdescr ~cloc cname csort;
  mk_var cname |> mk_term ~tdescr:cdescr ~tloc:cloc
;;

let add_constraint (env : smt_env) (c : term) =
  env.ctx <- (mk_assert c |> mk_command) :: env.ctx
;;

let is_symbolic syms x = VarMap.mem x syms

let is_var (tm : SmtLang.term) =
  match tm.t with
  | Var _ -> true
  | _ -> false
;;

let rec ty_to_sort (ty : Nv_lang.Syntax.ty) : sort =
  let open Nv_lang.Syntax in
  match ty with
  | TVar { contents = Link t } -> ty_to_sort t
  | TUnit -> UnitSort
  | TBool -> BoolSort
  | TInt n -> if smt_config.infinite_arith then IntSort else BitVecSort n
  | TNode -> ty_to_sort (TInt 32)
  | TEdge -> ty_to_sort (TTuple [TNode; TNode])
  | TTuple ts ->
    (match ts with
    | [t] -> ty_to_sort t
    | ts ->
      let name = Nv_utils.OCamlUtils.oget (datatype_name ty) in
      DataTypeSort (name, BatList.map ty_to_sort ts))
  | TOption ty' ->
    let name = Nv_utils.OCamlUtils.oget (datatype_name ty) in
    DataTypeSort (name, [ty_to_sort ty'])
  | TMap _ -> failwith "unimplemented"
  (*       mk_array_sort ctx (ty_to_sort ctx ty1) (ty_to_sort ctx ty2)*)
  | TVar _ | QVar _ | TArrow _ | TRecord _ ->
    failwith
      (Printf.sprintf
         "internal error (ty_to_sort): %s"
         (Nv_lang.Printing.ty_to_string ty))
;;

(* Utilities *)

(** Naming convention of useful variables *)
let label_var i = Printf.sprintf "label-%d-" i

let node_of_label_var s = int_of_string (BatList.nth (BatString.split_on_char '-' s) 1)

let proj_of_var s =
  let name, _i = Var.from_var @@ Var.of_var_string s in
  try
    let _, s2 = BatString.split name "-proj-" in
    let s2 = List.hd @@ BatString.split_on_char '-' s2 in
    Some (int_of_string s2)
  with
  | Not_found -> None
;;

let assert_var i = Printf.sprintf "assert-%d" i

(* this is flaky, the variable name used by SMT will be
   assert-n-result, we need to chop both ends *)
let node_of_assert_var s = int_of_string (BatString.chop ~l:7 ~r:7 s)

let symbolic_of_proj_var s =
  let name, i = Var.from_var @@ Var.of_var_string s in
  try
    let s1, _ = BatString.split name "-proj-" in
    Var.to_var (s1, i)
  with
  | Not_found -> Var.to_var (name, i)
;;

let symbolic_var (s : Var.t) = Var.to_string s

(* parses the initial reply of the solver *)
let rec parse_reply (solver : solver_proc) =
  let r = get_reply solver in
  match r with
  | Some "sat" -> SAT
  | Some "unsat" -> UNSAT
  | Some "unknown" -> UNKNOWN
  | None -> OTHER "EOF"
  | Some r ->
    if BatString.starts_with r "(error"
    then Console.error ("Solver error: " ^ r)
    else print_endline r;
    parse_reply solver
;;
