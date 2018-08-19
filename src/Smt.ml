open Collections
open Unsigned
open Syntax
open Solution
open Z3

type smt_env =
  { solver: Z3.Solver.solver
  ; ctx: Z3.context
  ; symbolics: (Var.t * ty_or_exp) list }

let create_fresh descr s =
  Printf.sprintf "%s-%s" descr (Var.fresh s |> Var.to_string)

let create_name descr n =
  if descr = "" then Var.to_string n
  else Printf.sprintf "%s-%s" descr (Var.to_string n)

let mk_int_u32 ctx i =
  Expr.mk_numeral_string ctx (UInt32.to_string i)
    (Arithmetic.Integer.mk_sort ctx)

let mk_int ctx i = mk_int_u32 ctx (UInt32.of_int i)

let mk_bool ctx b = Boolean.mk_val ctx b

let add_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_add ctx [zero; zero] |> Expr.get_func_decl

let sub_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_sub ctx [zero; zero] |> Expr.get_func_decl

let lt_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_lt ctx zero zero |> Expr.get_func_decl

let le_f ctx =
  let zero = mk_int ctx 0 in
  Arithmetic.mk_le ctx zero zero |> Expr.get_func_decl

let eq_f ctx e = Boolean.mk_eq ctx e e |> Expr.get_func_decl

let and_f ctx =
  let tru = mk_bool ctx true in
  Boolean.mk_and ctx [tru; tru] |> Expr.get_func_decl

let or_f ctx =
  let tru = mk_bool ctx true in
  Boolean.mk_or ctx [tru; tru] |> Expr.get_func_decl

let not_f ctx =
  let tru = mk_bool ctx true in
  Boolean.mk_not ctx tru |> Expr.get_func_decl

let ite_f ctx e2 e3 =
  let tru = mk_bool ctx true in
  Boolean.mk_ite ctx tru e2 e3 |> Expr.get_func_decl

let peel ctx e = Z3Array.mk_select ctx e (mk_int ctx 0)

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
    | [] -> failwith "empty tuple"
    | [t] -> ty_to_smtlib t
    | t :: ts ->
        Printf.sprintf "Pair (%s) (%s)" (ty_to_smtlib t)
          (ty_to_smtlib (TTuple ts)) )
  | TOption ty -> Printf.sprintf "Option (%s)" (ty_to_smtlib ty)
  | TMap _ -> failwith "unimplemented"
  | TVar _ | QVar _ | TArrow _ ->
      failwith
        (Printf.sprintf "internal error (ty_to_smtlib): %s"
           (Printing.ty_to_string ty))

let mk_array_sort ctx sort1 sort2 = Z3Array.mk_sort ctx sort1 sort2

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
        Z3.Datatype.mk_constructor_s ctx "some" issome [v] [Some ty]
          [0]
      in
      let none =
        Z3.Datatype.mk_constructor_s ctx "none" isnone [] [] []
      in
      let name = Printf.sprintf "Option%s" (Z3.Sort.to_string ty) in
      Z3.Datatype.mk_sort_s ctx name [none; some]
  | TBool -> Z3.Boolean.mk_sort ctx
  | TTuple ts ->
      let len = List.length ts in
      let istup = Z3.Symbol.mk_string ctx "is-pair" in
      let getters =
        List.mapi
          (fun i _ ->
            Z3.Symbol.mk_string ctx (Printf.sprintf "proj%d" i) )
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
  | TMap (ty1, ty2) ->
      mk_array_sort ctx (ty_to_sort ctx ty1) (ty_to_sort ctx ty2)
  | TVar _ | QVar _ | TArrow _ ->
      failwith "internal error (ty_to_sort)"

let mk_array ctx sort value = Z3Array.mk_const_array ctx sort value

type array_info =
  { f: Sort.sort -> Sort.sort
  ; make: Expr.expr -> Expr.expr
  ; lift: bool }

let is_symbolic syms x =
  List.exists (fun (y, e) -> Var.equals x y) syms

let rec encode_exp_z3 descr env arr (e: exp) =
  (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ; *)
  match e.e with
  | EVar x ->
      let name =
        if is_symbolic env.symbolics x then Var.to_string x
        else create_name descr x
      in
      let sort = ty_to_sort env.ctx (oget e.ety) |> arr.f in
      Z3.Expr.mk_const_s env.ctx name sort
  | EVal v -> encode_value_z3 descr env arr v
  | EOp (op, es) -> (
    match (op, es) with
    | And, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (and_f env.ctx) [e1; e2]
          else fun e1 e2 -> Boolean.mk_and env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | Or, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (or_f env.ctx) [e1; e2]
          else fun e1 e2 -> Boolean.mk_or env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | Not, _ ->
        let ze = List.hd es |> encode_exp_z3 descr env arr in
        if arr.lift then Z3Array.mk_map env.ctx (not_f env.ctx) [ze]
        else Boolean.mk_not env.ctx ze
    | UAdd, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (add_f env.ctx) [e1; e2]
          else fun e1 e2 -> Arithmetic.mk_add env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | USub, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (sub_f env.ctx) [e1; e2]
          else fun e1 e2 -> Arithmetic.mk_sub env.ctx [e1; e2]
        in
        encode_op_z3 descr env f arr es
    | UEq, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx
              (eq_f env.ctx (peel env.ctx e1))
              [e1; e2]
          else Boolean.mk_eq env.ctx
        in
        encode_op_z3 descr env f arr es
    | ULess, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (lt_f env.ctx) [e1; e2]
          else Arithmetic.mk_lt env.ctx
        in
        encode_op_z3 descr env f arr es
    | ULeq, _ ->
        let f =
          if arr.lift then fun e1 e2 ->
            Z3Array.mk_map env.ctx (le_f env.ctx) [e1; e2]
          else Arithmetic.mk_le env.ctx
        in
        encode_op_z3 descr env f arr es
    | MCreate, [e1] ->
        if arr.lift then failwith "not supported yet" ;
        let e1 = encode_exp_z3 descr env arr e1 in
        let sort = Arithmetic.Integer.mk_sort env.ctx |> arr.f in
        Z3Array.mk_const_array env.ctx sort e1
    | MGet, [e1; e2] ->
        if arr.lift then failwith "not supported yet" ;
        let e1 = encode_exp_z3 descr env arr e1 in
        let e2 = encode_exp_z3 descr env arr e2 in
        Z3Array.mk_select env.ctx e1 e2
    | MSet, [e1; e2; e3] ->
        if arr.lift then failwith "not supported yet" ;
        let e1 = encode_exp_z3 descr env arr e1 in
        let e2 = encode_exp_z3 descr env arr e2 in
        let e3 = encode_exp_z3 descr env arr e3 in
        Z3Array.mk_store env.ctx e1 e2 e3
    | MMap, [{e= EFun {arg= x; argty= ty1; resty= ty2; body= e1}}; e2] ->
        let e, _ = make_map env descr arr x (e1, ty1) e2 in
        e
    | ( MMapFilter
      , [ {e= EFun {arg= k; argty= kty; resty= vty; body= ke}}
        ; {e= EFun {arg= x; argty= ty1; resty= ty2; body= e1}}
        ; e2 ] ) ->
        let e, eparam = make_map env descr arr x (e1, ty1) e2 in
        let name = Var.fresh "map-result" |> Var.to_string in
        let name = if descr = "" then name else descr ^ "-" ^ name in
        let result =
          Expr.mk_const_s env.ctx name (Expr.get_sort e)
        in
        add env.solver [Boolean.mk_eq env.ctx result e] ;
        let i = Var.fresh "i" |> Var.to_string in
        let i = Symbol.mk_string env.ctx i in
        let iarg =
          Expr.mk_const env.ctx i (ty_to_sort env.ctx (oget kty))
        in
        let nname = Var.fresh "map-if-result" |> Var.to_string in
        let nname =
          if descr = "" then name else descr ^ "-" ^ nname
        in
        let nresult =
          Expr.mk_const_s env.ctx nname (Expr.get_sort e)
        in
        let cond = encode_exp_z3 descr env arr ke in
        let body =
          Boolean.mk_ite env.ctx cond
            (Boolean.mk_eq env.ctx
               (Z3Array.mk_select env.ctx nresult iarg)
               (Z3Array.mk_select env.ctx result iarg))
            (Boolean.mk_eq env.ctx
               (Z3Array.mk_select env.ctx nresult iarg)
               (Z3Array.mk_select env.ctx eparam iarg))
        in
        (* note: do not use mk_forall, appears to be broken *)
        let q =
          Quantifier.mk_forall_const env.ctx [iarg] body None [] []
            None None
          |> Quantifier.expr_of_quantifier
        in
        add env.solver [q] ;
        nresult
    | ( MMerge
      , [ { e=
              EFun
                { arg= x
                ; argty= ty1
                ; body= {e= EFun {arg= y; argty= ty2; body= e1}} } }
        ; e2
        ; e3 ] ) ->
        let keysort =
          match get_inner_type (oget e2.ety) with
          | TMap (ty, _) -> ty_to_sort env.ctx ty
          | _ -> failwith "internal error (encode_exp_z3)"
        in
        let arr2 =
          { f= (fun s -> mk_array_sort env.ctx keysort (arr.f s))
          ; make= (fun e -> mk_array env.ctx keysort (arr.make e))
          ; lift= true }
        in
        let e1 = encode_exp_z3 descr env arr2 e1 in
        let e2 = encode_exp_z3 descr env arr e2 in
        let e3 = encode_exp_z3 descr env arr e3 in
        let x = create_name descr x in
        let xty = ty_to_sort env.ctx (oget ty1) |> arr2.f in
        let xarg = Expr.mk_const_s env.ctx x xty in
        let y = create_name descr y in
        let yty = ty_to_sort env.ctx (oget ty2) |> arr2.f in
        let yarg = Expr.mk_const_s env.ctx y yty in
        Solver.add env.solver [Boolean.mk_eq env.ctx xarg e2] ;
        Solver.add env.solver [Boolean.mk_eq env.ctx yarg e3] ;
        e1
        (* let sort1 = ty_to_sort env.ctx (oget ty1) in
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
        Z3Array.mk_map env.ctx f [e2; e3] *)
    | _ -> failwith "internal error (encode_exp_z3)" )
  | EIf (e1, e2, e3) ->
      let ze1 = encode_exp_z3 descr env arr e1 in
      let ze2 = encode_exp_z3 descr env arr e2 in
      let ze3 = encode_exp_z3 descr env arr e3 in
      if arr.lift then
        Z3Array.mk_map env.ctx
          (ite_f env.ctx (peel env.ctx ze2) (peel env.ctx ze3))
          [ze1; ze2; ze3]
      else Boolean.mk_ite env.ctx ze1 ze2 ze3
  | ELet (x, e1, e2) ->
      let xstr = create_name descr x in
      let za =
        Expr.mk_const_s env.ctx xstr
          (oget e1.ety |> ty_to_sort env.ctx |> arr.f)
      in
      let ze1 = encode_exp_z3 descr env arr e1 in
      let ze2 = encode_exp_z3 descr env arr e2 in
      add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      ze2
  | ETuple es -> (
      let ty = oget e.ety in
      match ty with
      | TTuple ts ->
          let pair_sort = ty_to_sort env.ctx ty in
          let zes = List.map (encode_exp_z3 descr env arr) es in
          let f = Datatype.get_constructors pair_sort |> List.hd in
          if arr.lift then Z3Array.mk_map env.ctx f zes
          else Expr.mk_app env.ctx f zes
      | _ -> failwith "internal error (encode_exp_z3)" )
  | ESome e1 ->
      let ty = oget e.ety |> ty_to_sort env.ctx in
      let f = List.nth (Datatype.get_constructors ty) 1 in
      let ze = encode_exp_z3 descr env arr e1 in
      if arr.lift then Z3Array.mk_map env.ctx f [ze]
      else Expr.mk_app env.ctx f [ze]
  | EMatch (e, bs) ->
      let name = create_fresh descr "match" in
      let za =
        Expr.mk_const_s env.ctx name
          (oget e.ety |> ty_to_sort env.ctx |> arr.f)
      in
      let ze1 = encode_exp_z3 descr env arr e in
      add env.solver [Boolean.mk_eq env.ctx za ze1] ;
      encode_branches_z3 descr env arr za bs (oget e.ety)
  | ETy (e, ty) -> encode_exp_z3 descr env arr e
  | EFun _ | EApp _ -> failwith "function in smt encoding"

and make_map env descr arr x (e1, ty1) e2 =
  let keysort =
    match get_inner_type (oget e2.ety) with
    | TMap (ty, _) -> ty_to_sort env.ctx ty
    | _ -> failwith "internal error (encode_exp_z3)"
  in
  let arr2 =
    { f= (fun s -> mk_array_sort env.ctx keysort (arr.f s))
    ; make= (fun e -> mk_array env.ctx keysort (arr.make e))
    ; lift= true }
  in
  let e1 = encode_exp_z3 descr env arr2 e1 in
  let e2 = encode_exp_z3 descr env arr e2 in
  let x = create_name descr x in
  let xty = ty_to_sort env.ctx (oget ty1) |> arr2.f in
  let xarg = Expr.mk_const_s env.ctx x xty in
  Solver.add env.solver [Boolean.mk_eq env.ctx xarg e2] ;
  (e1, xarg)

and encode_op_z3 descr env f arr es =
  match es with
  | [] -> failwith "internal error (encode_op)"
  | [e] -> encode_exp_z3 descr env arr e
  | e :: es ->
      let ze1 = encode_exp_z3 descr env arr e in
      let ze2 = encode_op_z3 descr env f arr es in
      f ze1 ze2

and encode_branches_z3 descr env arr name bs (t: ty) =
  match List.rev bs with
  | [] -> failwith "internal error (encode_branches)"
  | (p, e) :: bs ->
      let ze = encode_exp_z3 descr env arr e in
      (* we make the last branch fire no matter what *)
      let _ = encode_pattern_z3 descr env arr name p t in
      encode_branches_aux_z3 descr env arr name (List.rev bs) ze t

(* I'm assuming here that the cases are exhaustive *)
and encode_branches_aux_z3 descr env arr name bs accze (t: ty) =
  match bs with
  | [] -> accze
  | (p, e) :: bs ->
      let ze = encode_exp_z3 descr env arr e in
      let zp = encode_pattern_z3 descr env arr name p t in
      let ze =
        if arr.lift then
          Z3Array.mk_map env.ctx
            (ite_f env.ctx (peel env.ctx ze) (peel env.ctx accze))
            [zp; ze; accze]
        else Boolean.mk_ite env.ctx zp ze accze
      in
      encode_branches_aux_z3 descr env arr name bs ze t

and encode_pattern_z3 descr env arr zname p (t: ty) =
  let ty = get_inner_type t in
  match (p, ty) with
  | PWild, _ ->
      if arr.lift then arr.make (mk_bool env.ctx true)
      else Boolean.mk_true env.ctx
  | PVar x, t ->
      let local_name = create_name descr x in
      let za =
        Expr.mk_const_s env.ctx local_name
          (ty_to_sort env.ctx t |> arr.f)
      in
      add env.solver [Boolean.mk_eq env.ctx za zname] ;
      if arr.lift then arr.make (mk_bool env.ctx true)
      else Boolean.mk_true env.ctx
  | PBool b, TBool ->
      if arr.lift then
        let a = arr.make (mk_bool env.ctx b) in
        Z3Array.mk_map env.ctx
          (eq_f env.ctx (peel env.ctx zname))
          [zname; a]
      else Boolean.mk_eq env.ctx zname (Boolean.mk_val env.ctx b)
  | PUInt32 i, TInt _ ->
      if arr.lift then
        let a = arr.make (mk_int_u32 env.ctx i) in
        Z3Array.mk_map env.ctx
          (eq_f env.ctx (peel env.ctx zname))
          [zname; a]
      else
        let const = mk_int_u32 env.ctx i in
        Boolean.mk_eq env.ctx zname const
  | PTuple ps, TTuple ts -> (
    match (ps, ts) with
    | [p], [t] -> encode_pattern_z3 descr env arr zname p t
    | ps, ts ->
        let znames =
          List.mapi
            (fun i t ->
              let sort = ty_to_sort env.ctx t |> arr.f in
              ( Expr.mk_const_s env.ctx
                  (Printf.sprintf "elem%d" i |> create_fresh descr)
                  sort
              , sort
              , t ) )
            ts
        in
        let tup_sort = ty_to_sort env.ctx ty in
        let fs = Datatype.get_accessors tup_sort |> List.concat in
        List.combine znames fs
        |> List.iter (fun ((elem, _, _), f) ->
               let e =
                 if arr.lift then Z3Array.mk_map env.ctx f [zname]
                 else Expr.mk_app env.ctx f [zname]
               in
               add env.solver [Boolean.mk_eq env.ctx elem e] ) ;
        let matches =
          List.map
            (fun (p, (zname, _, ty)) ->
              encode_pattern_z3 descr env arr zname p ty )
            (List.combine ps znames)
        in
        let f acc e =
          if arr.lift then
            Z3Array.mk_map env.ctx (and_f env.ctx) [acc; e]
          else Boolean.mk_and env.ctx [acc; e]
        in
        let b = mk_bool env.ctx true in
        let base = if arr.lift then arr.make b else b in
        List.fold_left f base matches )
  | POption None, TOption _ ->
      let opt_sort = ty_to_sort env.ctx t in
      let f = Datatype.get_recognizers opt_sort |> List.hd in
      if arr.lift then Z3Array.mk_map env.ctx f [zname]
      else Expr.mk_app env.ctx f [zname]
  | POption (Some p), TOption t ->
      let new_name = create_fresh descr "option" in
      let za =
        Expr.mk_const_s env.ctx new_name
          (ty_to_sort env.ctx t |> arr.f)
      in
      let opt_sort = ty_to_sort env.ctx ty in
      let get_val =
        Datatype.get_accessors opt_sort |> List.concat |> List.hd
      in
      let is_some = List.nth (Datatype.get_recognizers opt_sort) 1 in
      let e =
        if arr.lift then Z3Array.mk_map env.ctx get_val [zname]
        else Expr.mk_app env.ctx get_val [zname]
      in
      add env.solver [Boolean.mk_eq env.ctx za e] ;
      let zp = encode_pattern_z3 descr env arr za p t in
      if arr.lift then
        let e = Z3Array.mk_map env.ctx is_some [zname] in
        Z3Array.mk_map env.ctx (and_f env.ctx) [e; zp]
      else
        Boolean.mk_and env.ctx
          [Expr.mk_app env.ctx is_some [zname]; zp]
  | _ ->
      Console.error
        (Printf.sprintf "internal error (encode_pattern): (%s, %s)"
           (Printing.pattern_to_string p)
           (Printing.ty_to_string (get_inner_type t)))

and encode_value_z3 descr env arr (v: Syntax.value) =
  (* Printf.printf "value: %s\n" (Printing.value_to_string v) ; *)
  match v.v with
  | VBool b ->
      let b = mk_bool env.ctx b in
      if arr.lift then arr.make b else b
  | VUInt32 i ->
      let i = mk_int_u32 env.ctx i in
      if arr.lift then arr.make i else i
  | VTuple vs -> (
    match oget v.vty with
    | TTuple ts ->
        let pair_sort = ty_to_sort env.ctx (oget v.vty) in
        let zes = List.map (encode_value_z3 descr env arr) vs in
        let f = Datatype.get_constructors pair_sort |> List.hd in
        if arr.lift then Z3Array.mk_map env.ctx f zes
        else Expr.mk_app env.ctx f zes
    | _ -> failwith "internal error (encode_value)" )
  | VOption None ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = Datatype.get_constructors opt_sort |> List.hd in
      let e = Expr.mk_app env.ctx f [] in
      if arr.lift then arr.make e else e
  | VOption (Some v1) ->
      let opt_sort = ty_to_sort env.ctx (oget v.vty) in
      let f = List.nth (Datatype.get_constructors opt_sort) 1 in
      let zv = encode_value_z3 descr env arr v1 in
      if arr.lift then Z3Array.mk_map env.ctx f [zv]
      else Expr.mk_app env.ctx f [zv]
  | VClosure _ -> failwith "internal error (closure in smt)"
  | VMap map ->
      if arr.lift then failwith "internal error (lifted vmap)" ;
      let bs, d = BddMap.bindings map in
      let zd = encode_value_z3 descr env arr d in
      let keysort =
        match get_inner_type (oget v.vty) with
        | TMap (ty, _) -> ty_to_sort env.ctx ty
        | _ -> failwith "internal error (encode_exp_value)"
      in
      let a = mk_array env.ctx keysort zd in
      List.fold_left
        (fun acc (kv, vv) ->
          let zk = encode_value_z3 descr env arr kv in
          let zv = encode_value_z3 descr env arr vv in
          Z3Array.mk_store env.ctx acc zk zv )
        a bs

let encode_exp_z3 env str e =
  Expr.simplify
    (encode_exp_z3 str env
       {f= (fun x -> x); make= (fun e -> e); lift= false}
       e)
    None

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
        Expr.mk_const_s env.ctx name
          (oget exp.ety |> ty_to_sort env.ctx)
      in
      let e = encode_exp_z3 env str exp in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, nodestr, xstr, ystr)
  | _ -> failwith "internal error (encode_z3_merge)"

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
        Expr.mk_const_s env.ctx name
          (oget exp.ety |> ty_to_sort env.ctx)
      in
      let e = encode_exp_z3 env str exp in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
      (result, edgestr, xstr)
  | _ -> failwith "internal error"

let encode_z3_init str env e =
  match e.e with
  | EFun {arg= node; argty= nodety; body= e} ->
      let nodestr =
        Expr.mk_const_s env.ctx (create_name str node)
          (ty_to_sort env.ctx (oget nodety))
      in
      let name = Printf.sprintf "%s-result" str in
      let result =
        Expr.mk_const_s env.ctx name
          (oget e.ety |> ty_to_sort env.ctx)
      in
      let e = encode_exp_z3 env str e in
      add env.solver [Boolean.mk_eq env.ctx result e] ;
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
      let v =
        Expr.mk_const_s env.ctx (Var.to_string v)
          (ty_to_sort env.ctx (oget e.ety))
      in
      let e = encode_exp_z3 env "" e in
      Solver.add env.solver [Boolean.mk_eq env.ctx v e] )
    sym_vars ;
  (* add the require clauses *)
  List.iter
    (fun e ->
      let e = encode_exp_z3 env "" e in
      Solver.add env.solver [e] )
    requires

let init_solver ds =
  Var.reset () ;
  let ctx = Z3.mk_context cfg in
  let t1 = Tactic.mk_tactic ctx "simplify" in
  let t2 = Tactic.mk_tactic ctx "propagate-values" in
  let t3 = Tactic.mk_tactic ctx "bit-blast" in
  let t4 = Tactic.mk_tactic ctx "smt" in
  let t =
    Tactic.and_then ctx t1
      (Tactic.and_then ctx t2 (Tactic.and_then ctx t3 t4 []) [])
      []
  in
  let solver = Z3.Solver.mk_solver_t ctx t in
  (* let solver = Z3.Solver.mk_solver ctx None in *)
  let symbolics = get_symbolics ds in
  let env = {solver; ctx; symbolics} in
  env

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
    add env.solver [Boolean.mk_eq env.ctx n (mk_int env.ctx i)] ;
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
      let ie = mk_int_u32 env.ctx i in
      let je = mk_int_u32 env.ctx j in
      let pair_sort =
        ty_to_sort env.ctx
          (TTuple [TInt (UInt32.of_int 32); TInt (UInt32.of_int 32)])
      in
      let f = Datatype.get_constructors pair_sort |> List.hd in
      add env.solver
        [Boolean.mk_eq env.ctx e (Expr.mk_app env.ctx f [ie; je])] ;
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
          add env.solver [Boolean.mk_eq env.ctx trans x] ;
          add env.solver [Boolean.mk_eq env.ctx acc y] ;
          add env.solver [Boolean.mk_eq env.ctx n (mk_int env.ctx i)] ;
          merge_result )
        init in_edges
    in
    let l =
      Expr.mk_const_s env.ctx
        (Printf.sprintf "label-%d" i)
        (ty_to_sort env.ctx aty)
    in
    add env.solver [Boolean.mk_eq env.ctx l merged] ;
    labelling := Graph.VertexMap.add (UInt32.of_int i) l !labelling
  done ;
  (* Propagate labels across edges outputs *)
  EdgeMap.iter
    (fun (i, j) x ->
      let label = Graph.VertexMap.find i !labelling in
      add env.solver [Boolean.mk_eq env.ctx label x] )
    !trans_input_map ;
  (* add assertions at the end *)
  ( match eassert with
  | None -> ()
  | Some eassert ->
      let all_good = ref (mk_bool env.ctx true) in
      for i = 0 to UInt32.to_int nodes - 1 do
        let label =
          Graph.VertexMap.find (UInt32.of_int i) !labelling
        in
        let result, n, x =
          encode_z3_assert (Printf.sprintf "assert-%d" i) env eassert
        in
        add env.solver [Boolean.mk_eq env.ctx x label] ;
        add env.solver [Boolean.mk_eq env.ctx n (mk_int env.ctx i)] ;
        let assertion_holds =
          Boolean.mk_eq env.ctx result (mk_bool env.ctx true)
        in
        all_good :=
          Boolean.mk_and env.ctx [!all_good; assertion_holds]
      done ;
      add env.solver [Boolean.mk_not env.ctx !all_good] ) ;
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
    (TInt (UInt32.of_int 32), remaining)
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
    | ["Int"] -> TInt (UInt32.of_int 32)
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
    VUInt32 i |> value
  with _ ->
    let f = Expr.get_func_decl e in
    let es = Expr.get_args e in
    let name = FuncDecl.get_name f |> Symbol.to_string in
    match (name, es) with
    | "true", _ -> VBool true |> value
    | "false", _ -> VBool false |> value
    | "some", [e1] -> VOption (Some (z3_to_value m e1)) |> value
    | "none", _ -> VOption None |> value
    | "store", [e1; e2; e3] -> (
        let v1 = z3_to_value m e1 in
        let v2 = z3_to_value m e2 in
        let v3 = z3_to_value m e3 in
        match v1.v with
        | VMap m -> VMap (BddMap.update m v2 v3) |> value
        | _ -> raise Model_conversion )
    | "const", [e1] -> (
        let sort = Z3.Expr.get_sort e in
        let ty = sort_to_ty sort in
        match get_inner_type ty with
        | TMap (kty, _) ->
            let e1 = z3_to_value m e1 in
            VMap (BddMap.create ~key_ty:kty e1) |> value
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
            VClosure (env, func) |> value )
    | _ ->
        if String.length name >= 7 && String.sub name 0 7 = "mk-pair"
        then
          let es = List.map (z3_to_value m) es in
          VTuple es |> value
        else raise Model_conversion

and z3_to_exp m (e: Expr.expr) : Syntax.exp =
  try exp (EVal (z3_to_value m e)) with _ ->
    try
      let f = Expr.get_func_decl e in
      let es = Expr.get_args e in
      let name = FuncDecl.get_name f |> Symbol.to_string in
      match (name, es) with
      | "ite", [e1; e2; e3] ->
          exp (EIf (z3_to_exp m e1, z3_to_exp m e2, z3_to_exp m e3))
      | "not", [e1] -> exp (EOp (Not, [z3_to_exp m e1]))
      | "and", _ ->
          let base = exp (EVal (value (VBool true))) in
          List.fold_left
            (fun e1 e2 -> exp (EOp (And, [e1; z3_to_exp m e2])))
            base es
      | "or", _ ->
          let base = exp (EVal (value (VBool false))) in
          List.fold_left
            (fun e1 e2 -> exp (EOp (Or, [e1; z3_to_exp m e2])))
            base es
      | "=", [e1; e2] ->
          exp (EOp (UEq, [z3_to_exp m e1; z3_to_exp m e2]))
      | _ -> raise Model_conversion
    with _ -> exp (EVar (Var.create "key"))

type smt_result = Unsat | Unknown | Sat of Solution.t

let eval env m str ty =
  let l = Expr.mk_const_s env.ctx str (ty_to_sort env.ctx ty) in
  let e = Model.eval m l true |> oget in
  z3_to_value m e

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
      print_endline (Model.to_string m) ;
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

let symvar_assign ds : value StringMap.t option =
  let env = init_solver ds in
  let requires = Syntax.get_requires ds in
  add_symbolic_constraints env requires [] ;
  let q = Solver.check env.solver [] in
  match q with
  | UNSATISFIABLE -> None
  | UNKNOWN -> None
  | SATISFIABLE ->
      let m = Solver.get_model env.solver in
      match m with
      | None -> failwith "internal error (find_sym_init)"
      | Some m -> Some (build_symbolic_assignment env m)

let solve ?symbolic_vars ds =
  let sym_vars =
    match symbolic_vars with None -> [] | Some ls -> ls
  in
  let num_nodes, aty =
    match (get_nodes ds, get_attr_type ds) with
    | Some n, Some aty -> (n, aty)
    | _ -> failwith "internal error (encode)"
  in
  let eassert = get_assert ds in
  let env = encode_z3 ds sym_vars in
  (* print_endline (Solver.to_string env.solver) ; *)
  let q = Solver.check env.solver [] in
  match q with
  | UNSATISFIABLE -> Unsat
  | UNKNOWN -> Unknown
  | SATISFIABLE ->
      let m = Solver.get_model env.solver in
      build_result m env aty num_nodes eassert
