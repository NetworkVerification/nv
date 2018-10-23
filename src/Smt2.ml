open Collections
open Unsigned
open Syntax
open Solution
open Z3

type datatype_decl =
  { name         : string;
    params       : sort list;
    constructors : (constructor_decl) list
  }

and constructor_decl =
  { constr_name : string; (* name of constructor *)
    constr_args : (string * sort) list (* projection functions and their type *)
  }
   
and sort =
  | BoolSort
  | IntSort
  | ArraySort of sort * sort
  | DataTypeSort of string * (sort list)
  | VarSort of string
                  
type smt_term =
  | Int of string (* unbounded integers *)
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
  | Symbol of string
  | App of smt_term * (smt_term list)
         
type smt_env =
  { mutable ctx: smt_term list
  ; mutable const_decls: (string * sort) BatSet.t (* named constant and its sort *)
  ; mutable type_decls: (string, datatype_decl) BatMap.t
  ; symbolics: (Var.t * ty_or_exp) list }
  
let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n =
  if descr = "" then Var.to_string n
  else Printf.sprintf "%s-%s" descr (Var.to_string n)

let mk_int_u32 i =
  Int (UInt32.to_string i)

let mk_int i = mk_int_u32 (UInt32.of_int i)

let mk_bool b = Bool b

let mk_symb s = Symbol s
              
let mk_app f args =
  App (f, args)

let mk_and t1 t2 = And (t1, t2)

let mk_not t1 = Not t1
                 
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

(* Finds the declaration for the datatype of ty if it exists,
   otherwise it creates it and adds it to the env *)
let compute_decl (env : smt_env) ty =
  let name = datatype_name ty in
  match BatMap.Exceptionless.find name env.type_decls  with
  | None ->
     let decl = ty_to_type_decl ty in
     env.type_decls <- BatMap.add name decl env.type_decls;
     decl
  | Some decl -> decl

let add_constant (env : smt_env) name sort =
  env.const_decls <- BatSet.add (name, sort) env.const_decls

let mk_constant (env : smt_env) name sort =
  add_constant env name sort;
  Symbol name

let add_constraint (env : smt_env) (c : smt_term) =
  env.ctx <- c :: env.ctx
               
let mk_array ctx sort value = Z3Array.mk_const_array ctx sort value

type array_info =
  { f: Sort.sort -> Sort.sort
  ; make: Expr.expr -> Expr.expr
  ; lift: bool }

let get_constructors decl =
  decl.constructors

let get_projections (constr: constructor_decl) =
  constr.constr_args

let get_recognizer (constr : constructor_decl) =
  "is-" ^ constr.constr_name

let is_symbolic syms x =
  List.exists (fun (y, e) -> Var.equals x y) syms

let rec encode_exp_z3 descr env (e: exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ; *)
  match e.e with
  | EVar x ->
      let name =
        if is_symbolic env.symbolics x then
          begin
            Printf.printf "var:%s\n" (Var.to_string x);
            Var.to_string x
            end
        else create_name descr x
      in
      let sort = ty_to_sort (oget e.ety) in
      mk_constant env name sort
  | EVal v -> encode_value_z3 descr env v
  | EOp (op, es) -> (
    match (op, es) with
    | Syntax.And, [e1;e2] ->
       let ze1 = encode_exp_z3 descr env e1 in
       let ze2 = encode_exp_z3 descr env e2 in
       And (ze1, ze2)
    | Syntax.Or, [e1;e2] ->
       let ze1 = encode_exp_z3 descr env e1 in
       let ze2 = encode_exp_z3 descr env e2 in
       Or (ze1, ze2)
    | Not, _ ->
        let ze = List.hd es |> encode_exp_z3 descr env in
        Not ze
    | Syntax.UAdd, [e1;e2] ->
       let ze1 = encode_exp_z3 descr env e1 in
       let ze2 = encode_exp_z3 descr env e2 in
       Add (ze1, ze2)
    | Syntax.USub, [e1;e2] ->
       let ze1 = encode_exp_z3 descr env e1 in
       let ze2 = encode_exp_z3 descr env e2 in
       Sub (ze1, ze2)
    | UEq, [e1;e2] ->
       let ze1 = encode_exp_z3 descr env e1 in
       let ze2 = encode_exp_z3 descr env e2 in
       Eq (ze1, ze2)
    | ULess, [e1;e2] ->
       let ze1 = encode_exp_z3 descr env e1 in
       let ze2 = encode_exp_z3 descr env e2 in
       Lt (ze1, ze2)
    | ULeq, [e1;e2] ->
       let ze1 = encode_exp_z3 descr env e1 in
       let ze2 = encode_exp_z3 descr env e2 in
       Leq (ze1, ze2)
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
      Ite (ze1, ze2, ze3)
  | ELet (x, e1, e2) ->
      let xstr = create_name descr x in
      let za = mk_constant env xstr (oget e1.ety |> ty_to_sort) in
      let ze1 = encode_exp_z3 descr env e1 in
      let ze2 = encode_exp_z3 descr env e2 in
      add_constraint env (Eq (za,ze1));
      ze2
  | ETuple es -> (
      let ty = oget e.ety in
      match ty with
      | TTuple ts ->
         let pair_decl = compute_decl env ty in
         let zes = List.map (encode_exp_z3 descr env) es in
         let f = get_constructors pair_decl |> List.hd in
         App (Symbol f.constr_name, zes)
      | _ -> failwith "internal error (encode_exp_z3)" )
  | ESome e1 ->
     let ty = oget e.ety in
     let decl = compute_decl env ty in
     let f = List.nth (get_constructors decl) 1 in
     let ze = encode_exp_z3 descr env e1 in
     App (Symbol f.constr_name, [ze])
  | EMatch (e, bs) ->
      let name = create_fresh descr "match" in
      let za = mk_constant env name (ty_to_sort (oget e.ety)) in
      let ze1 = encode_exp_z3 descr env e in
      add_constraint env (Eq (za, ze1));
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
      let ze = Ite (zp, ze, accze) in
      encode_branches_aux_z3 descr env name bs ze t

and encode_pattern_z3 descr env zname p (t: ty) =
  let ty = get_inner_type t in
  match (p, ty) with
  | PWild, _ ->
       mk_bool true
  | PVar x, t ->
     let local_name = create_name descr x in
     let za = mk_constant env local_name (ty_to_sort t) in
      add_constraint env (Eq (za, zname));
      mk_bool true
  | PBool b, TBool ->
     Eq (zname, mk_bool b)
  | PUInt32 i, TInt _ ->
     let const = mk_int_u32 i in
     Eq (zname, const)
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
               let e = mk_app (Symbol f) [zname] in
               add_constraint env (Eq (elem, e)));
        let matches =
          List.map
            (fun (p, (zname, _, ty)) ->
              encode_pattern_z3 descr env zname p ty )
            (List.combine ps znames)
        in
        let f acc e = mk_and acc e in
        let b = mk_bool true in
        let base = b in
        List.fold_left f base matches )
  | POption None, TOption _ ->
      let opt_decl = compute_decl env ty in
      let f = opt_decl |> get_constructors |> List.hd |> get_recognizer in
       mk_app (Symbol f) [zname]
  | POption (Some p), TOption t ->
      let new_name = create_fresh descr "option" in
      let za = mk_constant env new_name (ty_to_sort t) in
      let opt_decl = compute_decl env ty in
      let some_cons = List.nth (opt_decl |> get_constructors) 1 in
      let get_some, _ = some_cons |> get_projections |> List.hd in
      let is_some = some_cons |> get_recognizer in
      let e = mk_app (Symbol get_some) [zname] in
      add_constraint env (Eq (za, e));
      let zp = encode_pattern_z3 descr env za p t in
      mk_and (mk_app (Symbol is_some) [zname]) zp
  | _ ->
      Console.error
        (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
           (Printing.pattern_to_string p)
           (Printing.ty_to_string (get_inner_type t)))

and encode_value_z3 descr env (v: Syntax.value) =
  (* Printf.printf "value: %s\n" (Printing.value_to_string v) ; *)
  match v.v with
  | VBool b ->
      mk_bool b
  | VUInt32 i ->
     mk_int_u32 i
  | VTuple vs -> (
    match oget v.vty with
    | TTuple ts ->
        let pair_decl = compute_decl env (oget v.vty) in
        let zes = List.map (encode_value_z3 descr env) vs in
        let f = (pair_decl |> get_constructors |> List.hd).constr_name in
        mk_app (Symbol f) zes
    | _ -> failwith "internal error (encode_value)" )
  | VOption None ->
     let opt_decl = compute_decl env (oget v.vty) in
     let f = (opt_decl |> get_constructors |> List.hd).constr_name in
     let e = Symbol f in
     e
  | VOption (Some v1) ->
     let opt_decl = compute_decl env (oget v.vty) in
     let f = (List.nth (opt_decl |> get_constructors) 1).constr_name in
     let zv = encode_value_z3 descr env v1 in
      mk_app (Symbol f) [zv]
  | VClosure _ -> failwith "internal error (closure in smt)"
  | VMap map -> failwith "not doing maps yet"

let exp_to_z3 = encode_exp_z3

let encode_z3_merge str env e =
  match e.e with
  | EFun
      { arg= node
      ; argty= nodety
      ; body=
          { e=
              EFun
                { arg= x
                ; argty= xty
                ; body= {e= EFun {arg= y; argty= yty; body= exp}} }
          } } ->
      let nodestr =
        mk_constant env (create_name str node) (ty_to_sort (oget nodety))
      in
      let xstr =
        mk_constant env (create_name str x) (ty_to_sort (oget xty))
      in
      let ystr =
        mk_constant env (create_name str y) (ty_to_sort (oget yty))
      in
      let name = Printf.sprintf "%s-result" str in
      let result = mk_constant env name (oget exp.ety |> ty_to_sort) in
      let e = encode_exp_z3 str env exp in
      add_constraint env (Eq (result, e));
      (result, nodestr, xstr, ystr)
  | _ -> failwith "internal error (encode_z3_merge)"

let encode_z3_trans str env e =
  match e.e with
  | EFun
      { arg= edge
      ; argty= edgety
      ; body= {e= EFun {arg= x; argty= xty; body= exp}} } ->
      let edgestr = mk_constant env (create_name str edge) (ty_to_sort (oget edgety))
      in
      let xstr = mk_constant env (create_name str x) (ty_to_sort  (oget xty))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        mk_constant env name (oget exp.ety |> ty_to_sort) in
      let e = encode_exp_z3 str env exp in
      add_constraint env (Eq (result, e));
      (result, edgestr, xstr)
  | _ -> failwith "internal error"

let encode_z3_init str env e =
  match e.e with
  | EFun {arg= node; argty= nodety; body= e} ->
     let nodestr = mk_constant env (create_name str node) (ty_to_sort (oget nodety)) in
      let name = Printf.sprintf "%s-result" str in
      let result = mk_constant env name (oget e.ety |> ty_to_sort) in
      let e = encode_exp_z3 str env e in
      add_constraint env (Eq (result, e));
      (result, nodestr)
  | _ -> failwith "internal error"

let encode_z3_assert = encode_z3_trans

module EdgeMap = Map.Make (struct
  type t = UInt32.t * UInt32.t

  let compare (a, b) (c, d) =
    let cmp = UInt32.compare a c in
    if cmp <> 0 then cmp else UInt32.compare b d
end)

let cfg = [("model_compress", "false")]

let add_symbolic_constraints env requires sym_vars =
  List.iter
    (fun (v, e) ->
      let v = mk_constant env (Var.to_string v) (ty_to_sort (oget e.ety)) in
      let e = encode_exp_z3 "" env e in
      add_constraint env (Eq (v,e))) sym_vars ;
  (* add the require clauses *)
  List.iter
    (fun e ->
      let e = encode_exp_z3 "" env e in
      add_constraint env e) requires

let init_solver ds =
  Var.reset () ;
  (* let ctx = Z3.mk_context cfg in *)
  (* let t1 = Tactic.mk_tactic ctx "simplify" in *)
  (* let t2 = Tactic.mk_tactic ctx "propagate-values" in *)
  (* let t3 = Tactic.mk_tactic ctx "bit-blast" in *)
  (* let t4 = Tactic.mk_tactic ctx "smt" in *)
  (* let t = *)
  (*   Tactic.and_then ctx t1 *)
  (*     (Tactic.and_then ctx t2 (Tactic.and_then ctx t3 t4 []) []) *)
  (*     [] *)
  (* in *)
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
  for i = 0 to UInt32.to_int nodes - 1 do
    let init, n =
      encode_z3_init (Printf.sprintf "init-%d" i) env einit
    in
    add_constraint env (Eq (n, mk_int i));
    init_map := Graph.VertexMap.add (UInt32.of_int i) init !init_map
  done ;
  (* map each edge to transfer function result *)
  let incoming_map = ref Graph.VertexMap.empty in
  let trans_map = ref EdgeMap.empty in
  let trans_input_map = ref EdgeMap.empty in
  List.iter
    (fun (i, j) ->
      ( try
          let idxs = Graph.VertexMap.find j !incoming_map in
          incoming_map :=
            Graph.VertexMap.add j ((i, j) :: idxs) !incoming_map
        with _ ->
          incoming_map :=
            Graph.VertexMap.add j [(i, j)] !incoming_map ) ;
      let trans, e, x =
        encode_z3_trans
          (Printf.sprintf "trans-%d-%d" (UInt32.to_int i)
             (UInt32.to_int j))
          env etrans
      in
      trans_input_map := EdgeMap.add (i, j) x !trans_input_map ;
      let ie = mk_int_u32 i in
      let je = mk_int_u32 j in
      let pair_decl = compute_decl env (TTuple [TInt 32; TInt 32]) in
      let f = (pair_decl |> get_constructors |> List.hd).constr_name in
      add_constraint env (Eq (e, mk_app (Symbol f) [ie; je])) ;
      trans_map := EdgeMap.add (i, j) trans !trans_map )
    edges ;
  (* compute the labelling as the merge of all inputs *)
  let labelling = ref Graph.VertexMap.empty in
  for i = 0 to UInt32.to_int nodes - 1 do
    let init = Graph.VertexMap.find (UInt32.of_int i) !init_map in
    let in_edges =
      try Graph.VertexMap.find (UInt32.of_int i) !incoming_map
      with Not_found -> []
    in
    let idx = ref 0 in
    let merged =
      List.fold_left
        (fun acc (x, y) ->
          incr idx ;
          let trans = EdgeMap.find (x, y) !trans_map in
          let str = Printf.sprintf "merge-%d-%d" i !idx in
          let merge_result, n, x, y =
            encode_z3_merge str env emerge
          in
          add_constraint env (Eq (trans, x));
          add_constraint env (Eq (acc, y));
          add_constraint env (Eq (n, mk_int i));
          merge_result )
        init in_edges
    in
    let l = mk_constant env (Printf.sprintf "label-%d" i) (ty_to_sort aty) in
    add_constraint env (Eq (l, merged));
    labelling := Graph.VertexMap.add (UInt32.of_int i) l !labelling
  done ;
  (* Propagate labels across edges outputs *)
  EdgeMap.iter
    (fun (i, j) x ->
      let label = Graph.VertexMap.find i !labelling in
      add_constraint env (Eq (label, x))) !trans_input_map ;
  (* add assertions at the end *)
  ( match eassert with
  | None -> ()
  | Some eassert ->
      let all_good = ref (mk_bool true) in
      for i = 0 to UInt32.to_int nodes - 1 do
        let label =
          Graph.VertexMap.find (UInt32.of_int i) !labelling
        in
        let result, n, x =
          encode_z3_assert (Printf.sprintf "assert-%d" i) env eassert
        in
        add_constraint env (Eq (x, label));
        add_constraint env (Eq (n, mk_int i));
        let assertion_holds = Eq (result, (mk_bool true)) in
        all_good :=
          mk_and !all_good assertion_holds
      done ;
      add_constraint env (mk_not !all_good)) ;
  (* add the symbolic variable constraints *)
  add_symbolic_constraints env (get_requires ds) sym_vars ;
  env

exception Model_conversion

let is_num (c: char) =
  c = '0' || c = '1' || c = '2' || c = '3' || c = '4' || c = '5'
  || c = '6' || c = '7' || c = '8' || c = '9'

let grab_int str : int * string =
  let len = String.length str in
  let idx = ref (-1) in
  for i = 0 to len - 1 do
    let c = str.[i] in
    if not (is_num c) && !idx < 0 then idx := i
  done ;
  let num = String.sub str 0 !idx in
  let remaining = String.sub str !idx (len - !idx) in
  (int_of_string num, remaining)

let starts_with s1 s2 =
  let len1 = String.length s1 in
  let len2 = String.length s2 in
  if len1 < len2 then false
  else
    let pfx = String.sub s1 0 len2 in
    pfx = s2

let rec parse_custom_type s : ty * string =
  let len = String.length s in
  if starts_with s "Option" then
    let remaining = String.sub s 6 (len - 6) in
    let ty, r = parse_custom_type remaining in
    (TOption ty, r)
  else if starts_with s "Pair" then
    let remaining = String.sub s 4 (len - 4) in
    let count, remaining = grab_int remaining in
    let tys, r = parse_list count remaining in
    (TTuple tys, r)
  else if starts_with s "Int" then
    let remaining =
      if len = 3 then "" else String.sub s 3 (len - 3)
    in
    (TInt 32, remaining)
  else if starts_with s "Bool" then
    let remaining =
      if len = 4 then "" else String.sub s 4 (len - 4)
    in
    (TBool, remaining)
  else failwith (Printf.sprintf "parse_custom_type: %s" s)

and parse_list n s =
  if n = 0 then ([], s)
  else
    let ty, s = parse_custom_type s in
    let rest, s = parse_list (n - 1) s in
    (ty :: rest, s)

let sort_to_ty s =
  let rec aux str =
    let has_parens = String.sub str 0 1 = "(" in
    let str =
      if has_parens then String.sub str 1 (String.length str - 2)
      else str
    in
    let strs = String.split_on_char ' ' str in
    match strs with
    | ["Int"] -> TInt 32
    | ["Bool"] -> TBool
    | ["Array"; k; v] -> TMap (aux k, aux v)
    | [x] ->
        let ty, _ = parse_custom_type x in
        ty
    | _ -> failwith "cannot convert SMT sort to type"
  in
  aux (Sort.to_string s)

let rec z3_to_value m (e: Expr.expr) : Syntax.value =
  try
    let i = UInt32.of_string (Expr.to_string e) in
    vint i
  with _ ->
    let f = Expr.get_func_decl e in
    let es = Expr.get_args e in
    let name = FuncDecl.get_name f |> Symbol.to_string in
    match (name, es) with
    | "true", _ -> vbool true
    | "false", _ -> vbool false
    | "some", [e1] -> voption (Some (z3_to_value m e1))
    | "none", _ -> voption None
    | "store", [e1; e2; e3] -> (
        let v1 = z3_to_value m e1 in
        let v2 = z3_to_value m e2 in
        let v3 = z3_to_value m e3 in
        match v1.v with
        | VMap m -> vmap (BddMap.update m v2 v3)
        | _ -> raise Model_conversion )
    | "const", [e1] -> (
        let sort = Z3.Expr.get_sort e in
        let ty = sort_to_ty sort in
        match get_inner_type ty with
        | TMap (kty, _) ->
            let e1 = z3_to_value m e1 in
            vmap (BddMap.create ~key_ty:kty e1)
        | _ -> failwith "internal error (z3_to_exp)" )
    | "as-array", _ -> (
        let x = FuncDecl.get_parameters f |> List.hd in
        let f = FuncDecl.Parameter.get_func_decl x in
        let y = Model.get_func_interp m f in
        match y with
        | None -> failwith "impossible"
        | Some x ->
            let e = Model.FuncInterp.get_else x in
            let e = z3_to_exp m e in
            let env = {ty= Env.empty; value= Env.empty} in
            let key = Var.create "key" in
            let func =
              {arg= key; argty= None; resty= None; body= e}
            in
            vclosure (env, func) )
    | _ ->
        if String.length name >= 7 && String.sub name 0 7 = "mk-pair"
        then
          let es = List.map (z3_to_value m) es in
          vtuple es
        else raise Model_conversion

and z3_to_exp m (e: Expr.expr) : Syntax.exp =
  try e_val (z3_to_value m e) with _ ->
    try
      let f = Expr.get_func_decl e in
      let es = Expr.get_args e in
      let name = FuncDecl.get_name f |> Symbol.to_string in
      match (name, es) with
      | "ite", [e1; e2; e3] ->
          eif (z3_to_exp m e1) (z3_to_exp m e2) (z3_to_exp m e3)
      | "not", [e1] -> eop Not [z3_to_exp m e1]
      | "and", e :: es ->
          let base = z3_to_exp m e in
          List.fold_left
            (fun e1 e2 -> eop And [e1; z3_to_exp m e2])
            base es
      | "or", e :: es ->
          let base = z3_to_exp m e in
          List.fold_left
            (fun e1 e2 -> eop Or [e1; z3_to_exp m e2])
            base es
      | "=", [e1; e2] -> eop UEq [z3_to_exp m e1; z3_to_exp m e2]
      | _ -> raise Model_conversion
    with _ -> evar (Var.create "key")

type smt_result = Unsat | Unknown | Sat of Solution.t

let eval env m str ty = failwith "not yet implemented"

let build_symbolic_assignment env m =
  let sym_map = ref StringMap.empty in
  List.iter
    (fun (x, e) ->
      let ty = match e with Ty ty -> ty | Exp e -> oget e.ety in
      let name = Var.to_string x in
      let e = eval env m name ty in
      sym_map := StringMap.add name e !sym_map )
    env.symbolics ;
  !sym_map

let build_result m env aty num_nodes eassert =
  match m with
  | None -> failwith "internal error (encode)"
  | Some m ->
      (* print_endline (Model.to_string m) ; *)
      let map = ref Graph.VertexMap.empty in
      (* grab the model from z3 *)
      for i = 0 to UInt32.to_int num_nodes - 1 do
        let e = eval env m (Printf.sprintf "label-%d" i) aty in
        map := Graph.VertexMap.add (UInt32.of_int i) e !map
      done ;
      let assertions =
        match eassert with
        | None -> None
        | Some _ ->
            let assertions = ref Graph.VertexMap.empty in
            for i = 0 to UInt32.to_int num_nodes - 1 do
              let e =
                eval env m
                  (Printf.sprintf "assert-%d-result" i)
                  TBool
              in
              match (e, eassert) with
              | {v= VBool b}, Some _ ->
                  assertions :=
                    Graph.VertexMap.add (UInt32.of_int i) b
                      !assertions
              | _ -> failwith "internal error (build_result)"
            done ;
            Some !assertions
      in
      let sym_map = build_symbolic_assignment env m in
      Sat {symbolics= sym_map; labels= !map; assertions}


module CompileSMT =
  struct

    let printList (printer: 'a -> string) (ls: 'a list) (first : string)
                  (sep : string) (last : string) =
      let rec loop ls =
        match ls with
        | [] -> ""
        | [l] -> printer l
        | l :: ls -> (printer l) ^ sep ^ (loop ls)
      in
      first ^ (loop ls) ^ last

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
                                        
    let rec term_to_smt (term : smt_term) : string =
      match term with
      | Int s -> s
      | Bool b -> if b then "true" else "false"
      | And (b1, b2) ->
         Printf.sprintf "(and %s %s)" (term_to_smt b1) (term_to_smt b2)
      | Or (b1, b2) ->
         Printf.sprintf "(or %s %s)" (term_to_smt b1) (term_to_smt b2)
      | Not b ->
         Printf.sprintf "(not %s)" (term_to_smt b)
      | Add (n, m) ->
         Printf.sprintf "(+ %s %s)" (term_to_smt n) (term_to_smt m)
      | Sub (n, m) ->
         Printf.sprintf "(- %s %s)" (term_to_smt n) (term_to_smt m)
      | Eq (n, m) ->
         Printf.sprintf "(= %s %s)" (term_to_smt n) (term_to_smt m)
      | Lt (n, m) ->
         Printf.sprintf "(< %s %s)" (term_to_smt n) (term_to_smt m)
      | Leq (n, m) ->
         Printf.sprintf "(<= %s %s)" (term_to_smt n) (term_to_smt m)         
      | Ite (t1, t2, t3) ->
         Printf.sprintf "(ite %s %s %s)" (term_to_smt t1) (term_to_smt t2) (term_to_smt t3)
      | Symbol s -> s
      | App (t, ts) when ts = [] -> (*this case may be redundant for our encoding *)
         Printf.sprintf "%s" (term_to_smt t) 
      | App (t, ts) ->
         let args = printList term_to_smt ts "" " " "" in 
         Printf.sprintf "(%s %s)" (term_to_smt t) args

    let constructor_to_smt (c: constructor_decl) : string =
      match c.constr_args with
      | [] -> c.constr_name
      | (p :: ps) ->
         let constrArgs = printList (fun (p,s) ->
                              Printf.sprintf "(%s %s)" p (sort_to_smt s)) (p :: ps) "" " " ""
         in
         Printf.sprintf "(%s %s)" c.constr_name constrArgs
                        
    let rec type_decl_to_smt (dt: datatype_decl) : string =
      Printf.sprintf "(declare-datatypes %s ((%s %s)))"
                     (printList sort_to_smt dt.params "(" " " ")")
                     dt.name
                     (printList constructor_to_smt dt.constructors "" " " "")

    let const_decl_to_smt (const_name, const_sort : string * sort) : string =
      Printf.sprintf "(declare-const %s %s)" const_name (sort_to_smt const_sort)

    let ctx_to_smt (tm: smt_term) : string =
      Printf.sprintf "(assert %s)" (term_to_smt tm)
      
    let env_to_smt (env : smt_env) =
      (* Emit type declarations *)
      let decls =
        BatMap.fold (fun typ acc ->
            (Printf.sprintf "%s\n" (type_decl_to_smt typ)) ^ acc) env.type_decls ""
      in
      (* Emit constants *)
      let constants =
        BatSet.fold (fun const acc ->
            (Printf.sprintf "%s\n" (const_decl_to_smt const)) ^ acc) env.const_decls ""
      in
      (* Emit context *)
      let context = printList ctx_to_smt env.ctx "\n" "\n" "\n" in
      Printf.sprintf "%s" (decls ^ constants ^ context)
  end

let solve ?symbolic_vars ds =
  let sym_vars =
    match symbolic_vars with None -> [] | Some ls -> ls
  in
  let env = encode_z3 ds sym_vars in
  let smt_query = CompileSMT.env_to_smt env in
  Printf.printf "%s" smt_query;
  Unsat
