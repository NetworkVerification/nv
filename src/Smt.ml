open Unsigned
open Syntax
open Z3

type ('a, 'b, 'c) smt_encoding =
  { merge: 'b
  ; merge_args: 'a list
  ; trans: 'b
  ; trans_args: 'a list
  ; init: 'b
  ; init_args: 'a list
  ; metadata: 'c }

type smtlib_encoding = (string, string, string) smt_encoding

type z3_encoding = (Z3.Symbol.symbol, Z3.Expr.expr, unit) smt_encoding

type smt_env = {solver: Z3.Solver.solver; ctx: Z3.context}

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
      let name = Printf.sprintf "Pair%s" name in
      Z3.Datatype.mk_sort_s ctx name [some]
  | TMap _ | TVar _ | QVar _ | TArrow _ ->
      Console.error "internal error (ty_to_sort)"


let create_const name ty =
  Printf.sprintf "\n(declare-const %s (%s))" name (ty_to_smtlib ty)


let rec encode_exp_z3 env (e: exp) =
  match e.e with
  | EVar x ->
      Z3.Expr.mk_const_s env.ctx (Var.to_string x)
        (ty_to_sort env.ctx (oget e.ety))
  | EVal v -> encode_value_z3 env v
  | EOp (op, es) -> (
    match op with
    | And -> encode_op_z3 env (fun e1 e2 -> Boolean.mk_and env.ctx [e1; e2]) es
    | Or -> encode_op_z3 env (fun e1 e2 -> Boolean.mk_or env.ctx [e1; e2]) es
    | Not ->
        let ze = List.hd es |> encode_exp_z3 env in
        Boolean.mk_not env.ctx ze
    | UAdd ->
        encode_op_z3 env (fun e1 e2 -> Arithmetic.mk_add env.ctx [e1; e2]) es
    | USub ->
        encode_op_z3 env (fun e1 e2 -> Arithmetic.mk_sub env.ctx [e1; e2]) es
    | UEq -> encode_op_z3 env (Boolean.mk_eq env.ctx) es
    | ULess -> encode_op_z3 env (Arithmetic.mk_lt env.ctx) es
    | ULeq -> encode_op_z3 env (Arithmetic.mk_le env.ctx) es
    | MCreate _ | MGet | MSet | MMap | MMerge ->
        Console.error "unsupported map operation" )
  | EIf (e1, e2, e3) ->
      let ze1 = encode_exp_z3 env e1 in
      let ze2 = encode_exp_z3 env e2 in
      let ze3 = encode_exp_z3 env e3 in
      Boolean.mk_ite env.ctx ze1 ze2 ze3
  | ELet (x, e1, e2) ->
      let xstr = Var.to_string x in
      let za =
        Expr.mk_const_s env.ctx xstr (oget e.ety |> ty_to_sort env.ctx)
      in
      let ze1 = encode_exp_z3 env e1 in
      let ze2 = encode_exp_z3 env e2 in
      Solver.add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      ze2
  | ETuple es -> (
      let ty = oget e.ety in
      match (es, ty) with
      | [e], _ -> encode_exp_z3 env e
      | _, TTuple ts ->
          let pair_sort = ty_to_sort env.ctx ty in
          let zes = List.map (encode_exp_z3 env) es in
          let f = Datatype.get_constructors pair_sort |> List.hd in
          Expr.mk_app env.ctx f zes
      | _ -> Console.error "internal error (encode_exp)" )
  | ESome e1 ->
      let ty = oget e.ety |> ty_to_sort env.ctx in
      let f = List.nth (Datatype.get_constructors ty) 1 in
      let ze = encode_exp_z3 env e1 in
      Expr.mk_app env.ctx f [ze]
  | EMatch (e, bs) ->
      let x = Var.fresh "match" in
      let name = Var.to_string x in
      let za =
        Expr.mk_const_s env.ctx name (oget e.ety |> ty_to_sort env.ctx)
      in
      let ze1 = encode_exp_z3 env e in
      Solver.add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      encode_branches_z3 env za bs (oget e.ety)
  | ETy (e, ty) -> encode_exp_z3 env e
  | EFun _ | EApp _ -> Console.error "function in smt encoding"


and encode_op_z3 env f es =
  match es with
  | [] -> Console.error "internal error (encode_op)"
  | [e] -> encode_exp_z3 env e
  | e :: es ->
      let ze1 = encode_exp_z3 env e in
      let ze2 = encode_op_z3 env f es in
      f ze1 ze2


and encode_branches_z3 env name bs (t: ty) =
  match List.rev bs with
  | [] -> Console.error "internal error (encode_branches)"
  | (p, e) :: bs ->
      let ze = encode_exp_z3 env e in
      (* we make the last branch fire no matter what *)
      let _ = encode_pattern_z3 env name p t in
      encode_branches_aux_z3 env name (List.rev bs) ze t


(* I'm assuming here that the cases are exhaustive *)
and encode_branches_aux_z3 env name bs accze (t: ty) =
  match bs with
  | [] -> accze
  | (p, e) :: bs ->
      let ze = encode_exp_z3 env e in
      let zp = encode_pattern_z3 env name p t in
      let ze = Boolean.mk_ite env.ctx zp ze accze in
      encode_branches_aux_z3 env name bs ze t


and encode_pattern_z3 env zname p (t: ty) =
  let ty = Typing.get_inner_type t in
  match (p, ty) with
  | PWild, _ -> Boolean.mk_true env.ctx
  | PVar x, t ->
      let local_name = Var.to_string x in
      let za = Expr.mk_const_s env.ctx local_name (ty_to_sort env.ctx t) in
      Solver.add env.solver [Boolean.mk_eq env.ctx za zname] ;
      Boolean.mk_true env.ctx
  | PBool b, TBool -> Boolean.mk_eq env.ctx zname (Boolean.mk_val env.ctx b)
  | PUInt32 i, TInt _ ->
      let const =
        Expr.mk_numeral_string env.ctx (UInt32.to_string i)
          (Arithmetic.Integer.mk_sort env.ctx)
      in
      Boolean.mk_eq env.ctx zname const
  | PTuple ps, TTuple ts -> (
    match (ps, ts) with
    | [p], [t] -> encode_pattern_z3 env zname p t
    | ps, ts ->
        let tup_sort = ty_to_sort env.ctx ty in
        let znames =
          List.mapi
            (fun i t ->
              let sort = ty_to_sort env.ctx t in
              ( Expr.mk_const_s env.ctx (Printf.sprintf "elem%d" i) sort
              , sort
              , t ) )
            ts
        in
        let fs = Datatype.get_accessors tup_sort |> List.concat in
        List.combine znames fs
        |> List.iter (fun ((elem, _, _), f) ->
               Solver.add env.solver
                 [Boolean.mk_eq env.ctx elem (Expr.mk_app env.ctx f [zname])]
           ) ;
        let matches =
          List.map
            (fun (p, (zname, _, ty)) -> encode_pattern_z3 env zname p ty)
            (List.combine ps znames)
        in
        List.fold_left
          (fun acc e -> Boolean.mk_and env.ctx [acc; e])
          (Boolean.mk_true env.ctx) matches )
  | POption None, TOption _ ->
      let opt_sort = ty_to_sort env.ctx t in
      let f = Datatype.get_recognizers opt_sort |> List.hd in
      Expr.mk_app env.ctx f [zname]
  | POption Some p, TOption t ->
      let new_name = Var.fresh "option" |> Var.to_string in
      let za = Expr.mk_const_s env.ctx new_name (ty_to_sort env.ctx t) in
      let opt_sort = ty_to_sort env.ctx ty in
      let get_val =
        Datatype.get_accessors opt_sort |> List.concat |> List.hd
      in
      let is_some = List.nth (Datatype.get_recognizers opt_sort) 1 in
      Solver.add env.solver
        [Boolean.mk_eq env.ctx za (Expr.mk_app env.ctx get_val [zname])] ;
      let zp = encode_pattern_z3 env za p t in
      Boolean.mk_and env.ctx [Expr.mk_app env.ctx is_some [zname]; zp]
  | _ ->
      Console.error
        (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
           (Printing.pattern_to_string p)
           (Printing.ty_to_string (Typing.get_inner_type t)))


and encode_value_z3 env (v: Syntax.value) =
  match v.v with
  | VBool true -> Boolean.mk_true env.ctx
  | VBool false -> Boolean.mk_false env.ctx
  | VUInt32 i ->
      Expr.mk_numeral_int env.ctx 1 (Arithmetic.Integer.mk_sort env.ctx)
  | VTuple vs -> (
    match oget v.vty with
    | TTuple ts ->
        let pair_sort = ty_to_sort env.ctx (oget v.vty) in
        let zes = List.map (encode_value_z3 env) vs in
        let f = Datatype.get_constructors pair_sort |> List.hd in
        Expr.mk_app env.ctx f zes
    | _ -> Console.error "internal error (encode_value)" )
  | VOption None ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = Datatype.get_constructors opt_sort |> List.hd in
      Expr.mk_app env.ctx f []
  | VOption Some v1 ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = List.nth (Datatype.get_constructors opt_sort) 1 in
      let zv = encode_value_z3 env v1 in
      Expr.mk_app env.ctx f [zv]
  | VClosure _ -> Console.error "internal error (closure in smt)"
  | VMap _ -> Console.error "unimplemented: map"


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


let cfg = [("model", "true"); ("proof", "false")]

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


let encode_z3 (ds: declarations) : z3_encoding =
  Var.reset () ;
  let ctx = Z3.mk_context cfg in
  let solver = Z3.Solver.mk_solver ctx None in
  let env = {solver; ctx} in
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
            let nodestr = Symbol.mk_string ctx (Var.to_string node) in
            let xstr = Symbol.mk_string ctx (Var.to_string x) in
            let ystr = Symbol.mk_string ctx (Var.to_string y) in
            let result =
              Expr.mk_const_s ctx "result" (oget exp.ety |> ty_to_sort ctx)
            in
            let e = Expr.simplify (encode_exp_z3 env exp) None in
            Solver.add solver [Boolean.mk_eq ctx result e] ;
            (e, nodestr, xstr, ystr)
        | _ -> Console.error "internal error"
      in
      let trans, tnode, z =
        match etrans.e with
        | EFun
            { arg= node
            ; argty= nodety
            ; body= {e= EFun {arg= x; argty= xty; body= exp}} } ->
            let nodestr = Symbol.mk_string ctx (Var.to_string node) in
            let xstr = Symbol.mk_string ctx (Var.to_string x) in
            let result =
              Expr.mk_const_s ctx "result" (oget exp.ety |> ty_to_sort ctx)
            in
            let e = Expr.simplify (encode_exp_z3 env exp) None in
            Solver.add solver [Boolean.mk_eq ctx result e] ;
            (e, nodestr, xstr)
        | _ -> Console.error "internal error"
      in
      let init, inode =
        match einit.e with
        | EFun {arg= node; argty= nodety; body= e} ->
            let nodestr = Symbol.mk_string ctx (Var.to_string node) in
            let result =
              Expr.mk_const_s ctx "result" (oget e.ety |> ty_to_sort ctx)
            in
            let e = Expr.simplify (encode_exp_z3 env e) None in
            Solver.add solver [Boolean.mk_eq ctx result e] ;
            (e, nodestr)
        | _ -> Console.error "internal error"
      in
      Printf.printf "solver:\n%s\n" (Z3.Solver.to_string solver) ;
      { merge
      ; merge_args= [mnode; x; y]
      ; trans
      ; trans_args= [tnode; z]
      ; init
      ; init_args= [inode]
      ; metadata= () }
  | _ -> Console.error "attribute type not declared: type attribute = ..."
