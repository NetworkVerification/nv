open Unsigned
open Syntax
open Z3

(* 
type ('a, 'b, 'c) smt_encoding =
  { merge: 'b
  ; merge_args: 'a list
  ; trans: 'b
  ; trans_args: 'a list
  ; init: 'b
  ; init_args: 'a list
  ; metadata: 'c }

type smtlib_encoding = (string, string, string) smt_encoding

let rec encode_exp (e: exp) : string * string =
  match e.e with
  | EVar x -> ("", Var.to_string x)
  | EVal v -> ("", encode_value v.v)
  | EOp (op, es) -> (
    match op with
    | And -> encode_op "and" es
    | Or -> encode_op "or" es
    | Not ->
        let a, e = List.hd es |> encode_exp in
        (a, Printf.sprintf "(not %s)" e)
    | UAdd -> encode_op "bvadd" es
    | USub -> encode_op "bvsub" es
    | UEq -> encode_op "=" es
    | ULess -> encode_op "bvult" es
    | ULeq -> encode_op "bvule" es
    | MCreate _ | MGet | MSet | MMap | MMerge ->
        Console.error "unsupported map operation" )
  | EIf (e1, e2, e3) ->
      let a1, e1 = encode_exp e1 in
      let a2, e2 = encode_exp e2 in
      let a3, e3 = encode_exp e3 in
      (a1 ^ a2 ^ a3, Printf.sprintf "(ite %s %s %s)" e1 e2 e3)
  | ELet (x, e1, e2) ->
      let xstr = Var.to_string x in
      let a = create_const xstr (oget e1.ety) in
      let a1, e1 = encode_exp e1 in
      let a2, e2 = encode_exp e2 in
      let a = Printf.sprintf "%s\n(assert (= %s %s))" a xstr e1 in
      (a ^ a1 ^ a2, e2)
  | ETuple es -> (
    match es with
    | [] -> Console.error "internal error (encode_exp)"
    | [e] -> encode_exp e
    | e :: es ->
        let a, e1 = encode_exp e in
        let b, e2 = encode_exp (ETuple es |> exp) in
        (a ^ b, Printf.sprintf "(mk-pair %s %s)" e1 e2) )
  | ESome e ->
      let a, e = encode_exp e in
      (a, Printf.sprintf "(some %s)" e)
  | EMatch (e, bs) ->
      let x = Var.fresh "match" in
      let name = Var.to_string x in
      let a = create_const name (oget e.ety) in
      let b, e1 = encode_exp e in
      let a = Printf.sprintf "%s%s\n(assert (= %s %s))" a b name e1 in
      let c, e = encode_branches name bs (oget e.ety) in
      (a ^ c, e)
  | ETy (e, ty) -> encode_exp e
  | EFun _ | EApp _ -> Console.error "function in smt encoding"


and encode_op op_str es =
  match es with
  | [] -> Console.error "internal error (encode_op)"
  | [e] -> encode_exp e
  | e :: es ->
      let a, e1 = encode_exp e in
      let b, e2 = encode_op op_str es in
      (a ^ b, Printf.sprintf "(%s %s %s)" op_str e1 e2)


and encode_branches name bs (t: ty) =
  match List.rev bs with
  | [] -> Console.error "internal error (encode_branches)"
  | (p, e) :: bs ->
      let b, e = encode_exp e in
      (* we make the last branch fire no matter what *)
      let c, _ = encode_pattern name p t in
      encode_branches_aux name (List.rev bs) (c ^ b, e) t


(* I'm assuming here that the cases are exhaustive *)
and encode_branches_aux name bs acc (t: ty) =
  let a, acc = acc in
  match bs with
  | [] -> (a, acc)
  | (p, e) :: bs ->
      let b, e = encode_exp e in
      let c, p = encode_pattern name p t in
      let acc = Printf.sprintf "(ite %s %s %s)" p e acc in
      encode_branches_aux name bs (c ^ b ^ a, acc) t


and encode_pattern name p (t: ty) =
  match (p, Typing.get_inner_type t) with
  | PWild, _ -> ("", "true")
  | PVar x, t ->
      let local_name = Var.to_string x in
      let a = create_const local_name t in
      let binding =
        Printf.sprintf "%s\n(assert (= %s %s))" a local_name name
      in
      (binding, "true")
  | PBool b, TBool -> ("", Printf.sprintf "(= %s %s)" name (string_of_bool b))
  | PUInt32 i, TInt _ ->
      ("", Printf.sprintf "(= %s %s)" name (UInt32.to_string i))
  | PTuple ps, TTuple ts -> (
    match (ps, ts) with
    | [p], [t] -> encode_pattern name p t
    | p :: ps, t :: ts ->
        let fst_name = Var.fresh "first" |> Var.to_string in
        let fst = create_const fst_name t in
        let snd_name = Var.fresh "second" |> Var.to_string in
        let snd = create_const snd_name (TTuple ts) in
        let fst_decl =
          Printf.sprintf "%s\n(assert (= %s (first %s)))" fst fst_name name
        in
        let snd_decl =
          Printf.sprintf "%s\n(assert (= %s (second %s)))" snd snd_name name
        in
        let a, p1 = encode_pattern fst_name p t in
        let b, p2 = encode_pattern snd_name (PTuple ps) (TTuple ts) in
        let condition = Printf.sprintf "(and %s %s)" p1 p2 in
        (fst_decl ^ snd_decl ^ a ^ b, condition)
    | _ -> Console.error "internal error (encode_pattern)" )
  | POption None, TOption _ -> ("", Printf.sprintf "(is-none %s)" name)
  | POption Some p, TOption t ->
      let new_name = Var.fresh "option" |> Var.to_string in
      let a = create_const new_name t in
      let a = Printf.sprintf "%s\n(assert (= %s (val %s)))" a new_name name in
      let b, p = encode_pattern new_name p t in
      (a ^ b, Printf.sprintf "(and (is-some %s) %s)" name p)
  | _ ->
      Console.error
        (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
           (Printing.pattern_to_string p)
           (Printing.ty_to_string (Typing.get_inner_type t)))


and encode_value v : string =
  match v with
  | VBool true -> "true"
  | VBool false -> "false"
  | VUInt32 i -> Printf.sprintf "(_ bv%d %s)" 32 (UInt32.to_string i)
  | VTuple vs -> (
    match vs with
    | [] -> Console.error "internal error (encode_value)"
    | [v] -> encode_value v.v
    | v :: vs ->
        Printf.sprintf "(mk-pair %s %s)" (encode_value v.v)
          (encode_value (VTuple vs)) )
  | VOption None -> "none"
  | VOption Some v -> Printf.sprintf "(some %s)" (encode_value v.v)
  | VClosure _ -> Console.error "internal error (closure in smt)"
  | VMap _ -> Console.error "unimplemented: map"


let defs =
  "(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))\n\
   (declare-datatypes (T) ((Option none (some (val T)))))"


let encode_smtlib (ds: declarations) : smtlib_encoding =
  Var.reset () ;
  match (get_merge ds, get_trans ds, get_init ds) with
  | Some emerge, Some etrans, Some einit ->
      let merge, mnode, x, y =
        match emerge.e with
        | EFun
            { arg= node
            ; argty= nodety
            ; body=
                { e=
                    EFun
                      { arg= x
                      ; argty= xty
                      ; body= {e= EFun {arg= y; argty= yty; body= exp}} } } } ->
            let nodestr = Var.to_string node in
            let xstr = Var.to_string x in
            let ystr = Var.to_string y in
            let xty, yty = (oget xty, oget yty) in
            let nparam = create_const nodestr (oget nodety) in
            let xparam = create_const xstr xty in
            let yparam = create_const ystr yty in
            let result = create_const "result" (oget exp.ety) in
            let a, e = encode_exp exp in
            ( Printf.sprintf "%s%s%s%s%s\n(assert (= result %s))" nparam xparam
                yparam a result e
            , nodestr
            , xstr
            , ystr )
        | _ -> Console.error "internal error"
      in
      let trans, tnode, z =
        match etrans.e with
        | EFun
            { arg= node
            ; argty= nodety
            ; body= {e= EFun {arg= x; argty= xty; body= exp}} } ->
            let nodestr = Var.to_string node in
            let xstr = Var.to_string x in
            let xty = oget xty in
            let nparam = create_const nodestr (oget nodety) in
            let xparam = create_const xstr xty in
            let result = create_const "result" (oget exp.ety) in
            let a, e = encode_exp exp in
            ( Printf.sprintf "%s%s%s%s\n(assert (= result %s))" nparam xparam a
                result e
            , nodestr
            , xstr )
        | _ -> Console.error "internal error"
      in
      let init, inode =
        match einit.e with
        | EFun {arg= node; argty= nodety; body= e} ->
            let nodestr = Var.to_string node in
            let nparam = create_const nodestr (oget nodety) in
            let result = create_const "result" (oget e.ety) in
            let a, e = encode_exp e in
            ( Printf.sprintf "%s%s%s\n(assert (= result %s))" nparam a result e
            , nodestr )
        | _ -> Console.error "internal error"
      in
      { merge
      ; merge_args= [mnode; x; y]
      ; trans
      ; trans_args= [tnode; z]
      ; init
      ; init_args= [inode]
      ; metadata= defs }
  | _ -> Console.error "attribute type not declared: type attribute = ..."
*)

type smt_env = {solver: Z3.Solver.solver; ctx: Z3.context}

let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n = Printf.sprintf "%s-%s" descr (Var.to_string n)

let z3_int ctx i =
  Expr.mk_numeral_string ctx (UInt32.to_string i)
    (Arithmetic.Integer.mk_sort ctx)

let add solver args =
  (* List.iter (fun e -> Printf.printf "(assert %s)\n" (Expr.to_string e)) args; *)
  Solver.add solver args

let rec ty_to_smtlib (ty: ty) : string =
  match ty with
  | TVar {contents= Link t} -> ty_to_smtlib t
  | TBool -> "Bool"
  | TInt i -> Printf.sprintf "_ BitVec %s" (UInt32.to_string i)
  | TTuple ts -> (
    match ts with
    | [] -> Console.error "empty tuple"
    | [t] -> ty_to_smtlib t
    | t :: ts ->
        Printf.sprintf "Pair (%s) (%s)" (ty_to_smtlib t)
          (ty_to_smtlib (TTuple ts)) )
  | TOption ty -> Printf.sprintf "Option (%s)" (ty_to_smtlib ty)
  | TMap _ -> Console.error "unimplemented"
  | TVar _ | QVar _ | TArrow _ ->
      Console.error
        (Printf.sprintf "internal error (ty_to_smtlib): %s"
           (Printing.ty_to_string ty))

let mk_array_sort ctx sort =
  Z3Array.mk_sort ctx (Arithmetic.Integer.mk_sort ctx) sort

let rec ty_to_sort ctx (ty: ty) : Z3.Sort.sort =
  match ty with
  | TVar {contents= Link t} -> ty_to_sort ctx t
  | TInt _ -> Z3.Arithmetic.Integer.mk_sort ctx
  | TOption t ->
      let issome = Z3.Symbol.mk_string ctx "is-some" in
      let isnone = Z3.Symbol.mk_string ctx "is-none" in
      let v = Z3.Symbol.mk_string ctx "val" in
      let ty = ty_to_sort ctx t in
      let some =
        Z3.Datatype.mk_constructor_s ctx "some" issome [v] [Some ty] [0]
      in
      let none = Z3.Datatype.mk_constructor_s ctx "none" isnone [] [] [] in
      let name = Printf.sprintf "Option%s" (Z3.Sort.to_string ty) in
      Z3.Datatype.mk_sort_s ctx name [none; some]
  | TBool -> Z3.Boolean.mk_sort ctx
  | TTuple ts ->
      let len = List.length ts in
      let istup = Z3.Symbol.mk_string ctx "is-pair" in
      let getters =
        List.mapi
          (fun i _ -> Z3.Symbol.mk_string ctx (Printf.sprintf "proj%d" i))
          ts
      in
      let tys = List.map (ty_to_sort ctx) ts in
      let tyso = List.map (fun x -> Some x) tys in
      let is = List.map (fun _ -> 0) ts in
      let some =
        Z3.Datatype.mk_constructor_s ctx
          (Printf.sprintf "mk-pair%d" len)
          istup getters tyso is
      in
      let name =
        List.fold_left (fun acc ty -> acc ^ Sort.to_string ty) "" tys
      in
      let name = Printf.sprintf "Pair%d%s" (List.length ts) name in
      Z3.Datatype.mk_sort_s ctx name [some]
  | TMap (i, t) -> mk_array_sort ctx (ty_to_sort ctx t)
  | TVar _ | QVar _ | TArrow _ -> Console.error "internal error (ty_to_sort)"

let create_const name ty =
  Printf.sprintf "\n(declare-const %s (%s))" name (ty_to_smtlib ty)

let rec encode_exp_z3 descr env (e: exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ; *)
  match e.e with
  | EVar x ->
      Z3.Expr.mk_const_s env.ctx (create_name descr x)
        (ty_to_sort env.ctx (oget e.ety))
  | EVal v -> encode_value_z3 descr env v
  | EOp (op, es) -> (
    match (op, es) with
    | And, _ ->
        encode_op_z3 descr env
          (fun e1 e2 -> Boolean.mk_and env.ctx [e1; e2])
          es
    | Or, _ ->
        encode_op_z3 descr env (fun e1 e2 -> Boolean.mk_or env.ctx [e1; e2]) es
    | Not, _ ->
        let ze = List.hd es |> encode_exp_z3 descr env in
        Boolean.mk_not env.ctx ze
    | UAdd, _ ->
        encode_op_z3 descr env
          (fun e1 e2 -> Arithmetic.mk_add env.ctx [e1; e2])
          es
    | USub, _ ->
        encode_op_z3 descr env
          (fun e1 e2 -> Arithmetic.mk_sub env.ctx [e1; e2])
          es
    | UEq, _ -> encode_op_z3 descr env (Boolean.mk_eq env.ctx) es
    | ULess, _ -> encode_op_z3 descr env (Arithmetic.mk_lt env.ctx) es
    | ULeq, _ -> encode_op_z3 descr env (Arithmetic.mk_le env.ctx) es
    | MCreate, [_; e2] ->
        let e2 = encode_exp_z3 descr env e2 in
        let sort = Arithmetic.Integer.mk_sort env.ctx in
        Z3Array.mk_const_array env.ctx sort e2
    | MGet, [e1; e2] ->
        let e1 = encode_exp_z3 descr env e1 in
        let e2 = encode_exp_z3 descr env e2 in
        Z3Array.mk_select env.ctx e1 e2
    | MSet, [e1; e2; e3] ->
        let e1 = encode_exp_z3 descr env e1 in
        let e2 = encode_exp_z3 descr env e2 in
        let e3 = encode_exp_z3 descr env e3 in
        Z3Array.mk_store env.ctx e1 e2 e3
    | MMap, [{e= EFun {arg= x; argty= ty1; resty= ty2; body= e1}}; e2] ->
        let sort1 = ty_to_sort env.ctx (oget ty1) in
        let e1 = encode_exp_z3 descr env e1 in
        let e2 = encode_exp_z3 descr env e2 in
        let name = create_fresh descr "map" in
        let x = create_name descr x in
        let x = Symbol.mk_string env.ctx x in
        let xarg = Expr.mk_const env.ctx x (ty_to_sort env.ctx (oget ty1)) in
        let f = FuncDecl.mk_func_decl_s env.ctx name [sort1] sort1 in
        let app = Expr.mk_app env.ctx f [xarg] in
        let body = Boolean.mk_eq env.ctx app e1 in
        (* note: do not use mk_forall, appears to be broken *)
        let q =
          Quantifier.mk_forall_const env.ctx [xarg] body None [] [] None None
          |> Quantifier.expr_of_quantifier
        in
        add env.solver [q] ;
        Z3Array.mk_map env.ctx f [e2]
    | ( MMerge
      , [ { e=
              EFun
                { arg= x
                ; argty= ty1
                ; body= {e= EFun {arg= y; argty= ty2; body= e1}} } }
        ; e2
        ; e3 ] ) ->
        let sort1 = ty_to_sort env.ctx (oget ty1) in
        let e1 = encode_exp_z3 descr env e1 in
        let e2 = encode_exp_z3 descr env e2 in
        let e3 = encode_exp_z3 descr env e3 in
        let name = create_fresh descr "combine" in
        let x = create_name descr x in
        let x = Symbol.mk_string env.ctx x in
        let y = create_name descr y in
        let y = Symbol.mk_string env.ctx y in
        let f = FuncDecl.mk_func_decl_s env.ctx name [sort1; sort1] sort1 in
        let xarg = Expr.mk_const env.ctx x (ty_to_sort env.ctx (oget ty1)) in
        let yarg = Expr.mk_const env.ctx y (ty_to_sort env.ctx (oget ty2)) in
        let app = Expr.mk_app env.ctx f [xarg; yarg] in
        let body = Boolean.mk_eq env.ctx app e1 in
        let q =
          Quantifier.mk_forall_const env.ctx [xarg; yarg] body None [] [] None
            None
          |> Quantifier.expr_of_quantifier
        in
        add env.solver [q] ;
        Z3Array.mk_map env.ctx f [e2; e3]
    | MFilter, _ | _ -> Console.error "unsupported map operation" )
  | EIf (e1, e2, e3) ->
      let ze1 = encode_exp_z3 descr env e1 in
      let ze2 = encode_exp_z3 descr env e2 in
      let ze3 = encode_exp_z3 descr env e3 in
      Boolean.mk_ite env.ctx ze1 ze2 ze3
  | ELet (x, e1, e2) ->
      let xstr = create_name descr x in
      let za =
        Expr.mk_const_s env.ctx xstr (oget e.ety |> ty_to_sort env.ctx)
      in
      let ze1 = encode_exp_z3 descr env e1 in
      let ze2 = encode_exp_z3 descr env e2 in
      add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      ze2
  | ETuple es -> (
      let ty = oget e.ety in
      match (es, ty) with
      | [e], _ -> encode_exp_z3 descr env e
      | _, TTuple ts ->
          let pair_sort = ty_to_sort env.ctx ty in
          let zes = List.map (encode_exp_z3 descr env) es in
          let f = Datatype.get_constructors pair_sort |> List.hd in
          Expr.mk_app env.ctx f zes
      | _ -> Console.error "internal error (encode_exp)" )
  | ESome e1 ->
      let ty = oget e.ety |> ty_to_sort env.ctx in
      let f = List.nth (Datatype.get_constructors ty) 1 in
      let ze = encode_exp_z3 descr env e1 in
      Expr.mk_app env.ctx f [ze]
  | EMatch (e, bs) ->
      let name = create_fresh descr "match" in
      let za =
        Expr.mk_const_s env.ctx name (oget e.ety |> ty_to_sort env.ctx)
      in
      let ze1 = encode_exp_z3 descr env e in
      add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      encode_branches_z3 descr env za bs (oget e.ety)
  | ETy (e, ty) -> encode_exp_z3 descr env e
  | EFun _ | EApp _ -> Console.error "function in smt encoding"

and encode_op_z3 descr env f es =
  match es with
  | [] -> Console.error "internal error (encode_op)"
  | [e] -> encode_exp_z3 descr env e
  | e :: es ->
      let ze1 = encode_exp_z3 descr env e in
      let ze2 = encode_op_z3 descr env f es in
      f ze1 ze2

and encode_branches_z3 descr env name bs (t: ty) =
  match List.rev bs with
  | [] -> Console.error "internal error (encode_branches)"
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
      let ze = Boolean.mk_ite env.ctx zp ze accze in
      encode_branches_aux_z3 descr env name bs ze t

and encode_pattern_z3 descr env zname p (t: ty) =
  let ty = Typing.get_inner_type t in
  match (p, ty) with
  | PWild, _ -> Boolean.mk_true env.ctx
  | PVar x, t ->
      let local_name = create_name descr x in
      let za = Expr.mk_const_s env.ctx local_name (ty_to_sort env.ctx t) in
      add env.solver [Boolean.mk_eq env.ctx za zname] ;
      Boolean.mk_true env.ctx
  | PBool b, TBool -> Boolean.mk_eq env.ctx zname (Boolean.mk_val env.ctx b)
  | PUInt32 i, TInt _ ->
      let const = z3_int env.ctx i in
      Boolean.mk_eq env.ctx zname const
  | PTuple ps, TTuple ts -> (
    match (ps, ts) with
    | [p], [t] -> encode_pattern_z3 descr env zname p t
    | ps, ts ->
        let tup_sort = ty_to_sort env.ctx ty in
        let znames =
          List.mapi
            (fun i t ->
              let sort = ty_to_sort env.ctx t in
              ( Expr.mk_const_s env.ctx
                  (Printf.sprintf "elem%d" i |> create_fresh descr)
                  sort
              , sort
              , t ) )
            ts
        in
        let fs = Datatype.get_accessors tup_sort |> List.concat in
        List.combine znames fs
        |> List.iter (fun ((elem, _, _), f) ->
               add env.solver
                 [Boolean.mk_eq env.ctx elem (Expr.mk_app env.ctx f [zname])]
           ) ;
        let matches =
          List.map
            (fun (p, (zname, _, ty)) -> encode_pattern_z3 descr env zname p ty)
            (List.combine ps znames)
        in
        List.fold_left
          (fun acc e -> Boolean.mk_and env.ctx [acc; e])
          (Boolean.mk_true env.ctx) matches )
  | POption None, TOption _ ->
      let opt_sort = ty_to_sort env.ctx t in
      let f = Datatype.get_recognizers opt_sort |> List.hd in
      Expr.mk_app env.ctx f [zname]
  | POption (Some p), TOption t ->
      let new_name = create_fresh descr "option" in
      let za = Expr.mk_const_s env.ctx new_name (ty_to_sort env.ctx t) in
      let opt_sort = ty_to_sort env.ctx ty in
      let get_val =
        Datatype.get_accessors opt_sort |> List.concat |> List.hd
      in
      let is_some = List.nth (Datatype.get_recognizers opt_sort) 1 in
      add env.solver
        [Boolean.mk_eq env.ctx za (Expr.mk_app env.ctx get_val [zname])] ;
      let zp = encode_pattern_z3 descr env za p t in
      Boolean.mk_and env.ctx [Expr.mk_app env.ctx is_some [zname]; zp]
  | _ ->
      Console.error
        (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
           (Printing.pattern_to_string p)
           (Printing.ty_to_string (Typing.get_inner_type t)))

and encode_value_z3 descr env (v: Syntax.value) =
  match v.v with
  | VBool true -> Boolean.mk_true env.ctx
  | VBool false -> Boolean.mk_false env.ctx
  | VUInt32 i -> z3_int env.ctx i
  | VTuple vs -> (
    match oget v.vty with
    | TTuple ts ->
        let pair_sort = ty_to_sort env.ctx (oget v.vty) in
        let zes = List.map (encode_value_z3 descr env) vs in
        let f = Datatype.get_constructors pair_sort |> List.hd in
        Expr.mk_app env.ctx f zes
    | _ -> Console.error "internal error (encode_value)" )
  | VOption None ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = Datatype.get_constructors opt_sort |> List.hd in
      Expr.mk_app env.ctx f []
  | VOption (Some v1) ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = List.nth (Datatype.get_constructors opt_sort) 1 in
      let zv = encode_value_z3 descr env v1 in
      Expr.mk_app env.ctx f [zv]
  | VClosure _ -> Console.error "internal error (closure in smt)"
  | VMap _ -> Console.error "unimplemented: map"

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
                ; body= {e= EFun {arg= y; argty= yty; body= exp}} } } } ->
      let nodestr =
        Expr.mk_const_s env.ctx (create_name str node)
          (ty_to_sort env.ctx (oget nodety))
      in
      let xstr =
        Expr.mk_const_s env.ctx (create_name str x)
          (ty_to_sort env.ctx (oget xty))
      in
      let ystr =
        Expr.mk_const_s env.ctx (create_name str y)
          (ty_to_sort env.ctx (oget yty))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        Expr.mk_const_s env.ctx name (oget exp.ety |> ty_to_sort env.ctx)
      in
      let e = Expr.simplify (encode_exp_z3 str env exp) None in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, nodestr, xstr, ystr)
  | _ -> Console.error "internal error"

let encode_z3_trans str env e =
  match e.e with
  | EFun
      { arg= edge
      ; argty= edgety
      ; body= {e= EFun {arg= x; argty= xty; body= exp}} } ->
      let edgestr =
        Expr.mk_const_s env.ctx (create_name str edge)
          (ty_to_sort env.ctx (oget edgety))
      in
      let xstr =
        Expr.mk_const_s env.ctx (create_name str x)
          (ty_to_sort env.ctx (oget xty))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        Expr.mk_const_s env.ctx name (oget exp.ety |> ty_to_sort env.ctx)
      in
      let e = Expr.simplify (encode_exp_z3 str env exp) None in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, edgestr, xstr)
  | _ -> Console.error "internal error"

let encode_z3_init str env e =
  match e.e with
  | EFun {arg= node; argty= nodety; body= e} ->
      let nodestr =
        Expr.mk_const_s env.ctx (create_name str node)
          (ty_to_sort env.ctx (oget nodety))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        Expr.mk_const_s env.ctx name (oget e.ety |> ty_to_sort env.ctx)
      in
      let e = Expr.simplify (encode_exp_z3 str env e) None in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, nodestr)
  | _ -> Console.error "internal error"

module NodeMap = Map.Make (struct
  type t = int

  let compare = compare
end)

module EdgeMap = Map.Make (struct
  type t = UInt32.t * UInt32.t

  let compare (a, b) (c, d) =
    let cmp = UInt32.compare a c in
    if cmp <> 0 then cmp else UInt32.compare b d
end)

let cfg = [("auto-config", "false")]

let encode_z3 (ds: declarations) : smt_env =
  Var.reset () ;
  let ctx = Z3.mk_context cfg in
  let t1 = Tactic.mk_tactic ctx "simplify" in
  let t2 = Tactic.mk_tactic ctx "propagate-values" in
  let t3 = Tactic.mk_tactic ctx "solve-eqs" in
  let t4 = Tactic.mk_tactic ctx "bit-blast" in
  let t5 = Tactic.mk_tactic ctx "smt" in
  let t =
    Tactic.and_then ctx t1
      (Tactic.and_then ctx t2
         (Tactic.and_then ctx t3 (Tactic.and_then ctx t4 t5 []) [])
         [])
      []
  in
  let solver = Z3.Solver.mk_solver_t ctx t in
  let env = {solver; ctx} in
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
  let init_map = ref NodeMap.empty in
  for i = 0 to UInt32.to_int nodes - 1 do
    let init, n = encode_z3_init (Printf.sprintf "init-%d" i) env einit in
    add env.solver [Boolean.mk_eq env.ctx n (z3_int env.ctx (UInt32.of_int i))] ;
    init_map := NodeMap.add i init !init_map
  done ;
  (* map each edge to transfer function result *)
  let incoming_map = ref NodeMap.empty in
  let trans_map = ref EdgeMap.empty in
  let trans_input_map = ref EdgeMap.empty in
  List.iter
    (fun (i, j) ->
      ( try
          let idxs = NodeMap.find (UInt32.to_int j) !incoming_map in
          incoming_map :=
            NodeMap.add (UInt32.to_int j) ((i, j) :: idxs) !incoming_map
        with _ ->
          incoming_map := NodeMap.add (UInt32.to_int j) [(i, j)] !incoming_map
      ) ;
      let trans, e, x =
        encode_z3_trans
          (Printf.sprintf "trans-%d-%d" (UInt32.to_int i) (UInt32.to_int j))
          env etrans
      in
      trans_input_map := EdgeMap.add (i, j) x !trans_input_map ;
      let ie = z3_int env.ctx i in
      let je = z3_int env.ctx j in
      let pair_sort =
        ty_to_sort env.ctx
          (TTuple [TInt (UInt32.of_int 32); TInt (UInt32.of_int 32)])
      in
      let f = Datatype.get_constructors pair_sort |> List.hd in
      add env.solver [Boolean.mk_eq env.ctx e (Expr.mk_app env.ctx f [ie; je])] ;
      trans_map := EdgeMap.add (i, j) trans !trans_map )
    edges ;
  (* compute the labelling as the merge of all inputs *)
  let labelling = ref NodeMap.empty in
  for i = 0 to UInt32.to_int nodes - 1 do
    let init = NodeMap.find i !init_map in
    let in_edges = NodeMap.find i !incoming_map in
    let idx = ref 0 in
    let merged =
      List.fold_left
        (fun acc (x, y) ->
          incr idx ;
          let trans = EdgeMap.find (x, y) !trans_map in
          let str = Printf.sprintf "merge-%d-%d" i !idx in
          let merge_result, n, x, y = encode_z3_merge str env emerge in
          add solver [Boolean.mk_eq ctx trans x] ;
          add solver [Boolean.mk_eq ctx acc y] ;
          add solver [Boolean.mk_eq ctx n (z3_int env.ctx (UInt32.of_int i))] ;
          merge_result )
        init in_edges
    in
    let l =
      Expr.mk_const_s ctx (Printf.sprintf "label-%d" i) (ty_to_sort ctx aty)
    in
    add solver [Boolean.mk_eq ctx l merged] ;
    labelling := NodeMap.add i l !labelling
  done ;
  (* Propagate labels across edges outputs *)
  EdgeMap.iter
    (fun (i, j) x ->
      let label = NodeMap.find (UInt32.to_int i) !labelling in
      add solver [Boolean.mk_eq ctx label x] )
    !trans_input_map ;
  env

let rec z3_to_exp (e: Expr.expr) : Syntax.exp option =
  try
    let i = UInt32.of_string (Expr.to_string e) in
    Some (EVal (VUInt32 i |> value) |> exp)
  with _ ->
    let f = Expr.get_func_decl e in
    let es = Expr.get_args e in
    let name = FuncDecl.get_name f |> Symbol.to_string in
    match name with
    | "true" -> Some (EVal (VBool true |> value) |> exp)
    | "false" -> Some (EVal (VBool false |> value) |> exp)
    | "some" -> (
        let e = z3_to_exp (List.hd es) in
        match e with None -> None | Some e -> Some (ESome e |> exp) )
    | "none" -> Some (EVal (VOption None |> value) |> exp)
    | _ ->
        if String.length name >= 7 && String.sub name 0 7 = "mk-pair" then
          let es = List.map z3_to_exp es in
          if
            List.exists
              (fun e -> match e with None -> true | Some _ -> false)
              es
          then None
          else Some (ETuple (List.map oget es) |> exp)
        else None

type smt_result = Unsat | Sat of exp option NodeMap.t | Unknown

let solve ds =
  let num_nodes, aty =
    match (get_nodes ds, get_attr_type ds) with
    | Some n, Some aty -> (n, aty)
    | _ -> Console.error "internal error (encode)"
  in
  let env = encode_z3 ds in
  (* Printf.printf "%s\n" (Solver.to_string env.solver) ; *)
  let q = Solver.check env.solver [] in
  match q with
  | UNSATISFIABLE -> Unsat
  | UNKNOWN -> Unknown
  | SATISFIABLE ->
      let m = Solver.get_model env.solver in
      match m with
      | None -> Console.error "internal error (encode)"
      | Some m ->
          (* Printf.printf "%s\n" (Model.to_string m); *)
          let map = ref NodeMap.empty in
          for i = 0 to UInt32.to_int num_nodes - 1 do
            let l =
              Expr.mk_const_s env.ctx
                (Printf.sprintf "label-%d" i)
                (ty_to_sort env.ctx aty)
            in
            let e = Model.eval m l true |> oget in
            let e = z3_to_exp e in
            map := NodeMap.add i e !map
          done ;
          Sat !map
