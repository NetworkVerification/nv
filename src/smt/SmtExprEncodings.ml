open Collections
open Syntax
open SmtLang
open SmtUtils

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
  val lift1: ('a -> 'b) -> 'a t -> 'b t
  val lift2: ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t
  val to_list : 'a t -> 'a list
  val combine_term: term t -> term
  val add_symbolic: smt_env -> Var.t t -> Syntax.ty_or_exp -> unit
  val init_solver: (Var.t * Syntax.ty_or_exp) list -> smt_env
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
          symbolic_var x
        end
      else create_name descr x
    in
    name

  let to_list x = [x]

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
    | TArrow _ | TVar _ | QVar _ | TRecord _ -> failwith "unsupported type in SMT"

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
    | TVar _ | QVar _ | TArrow _ | TRecord _ ->
       failwith
         (Printf.sprintf "internal error (ty_to_sort): %s"
            (Printing.ty_to_string ty))

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
    | TVar _ | QVar _ | TArrow _ | TMap _ | TRecord _ ->
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

  let add_symbolic (env : smt_env) (b: Var.t) (ety: Syntax.ty_or_exp) =
    ignore(match ety with
           | Ty ty -> compute_decl env ty
           | Exp e -> compute_decl env (oget e.ety));
    env.symbolics <- VarMap.add b ety env.symbolics

  let is_symbolic syms x =
    VarMap.mem x syms

  let is_var (tm: SmtLang.term) =
    match tm.t with
    | Var _ -> true
    | _ -> false

  let ty_to_sorts = ty_to_sort

  let rec encode_exp_z3 descr env (e: exp) : term =
    (* Printf.printf "expr: %s\n" (Printing.exp_to_string e) ; *)
    match e.e with
    | EVar x ->
      let name =
        if is_symbolic env.symbolics x then
          begin
            (* Printf.printf "var:%s\n" (Var.to_string x); *)
            symbolic_var x
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
    | ERecord _ | EProject _ -> failwith "record or projection in smt encoding"

  and encode_branches_z3 descr env names bs (t: ty) =
    match isEmptyBranch bs with
    | true -> failwith "internal error (encode_branches)"
    | false ->
      encode_branches_aux_z3 descr env names bs t

  (* I'm assuming here that the cases are exhaustive *)
  and encode_branches_aux_z3 descr env name bs (t: ty) =
    match popBranch bs with
    |  ((p,e), bs) when isEmptyBranch bs ->
      let _ = encode_pattern_z3 descr env name p t in
      let ze = encode_exp_z3 descr env e in
      ze
    | ((p,e), bs) ->
      let ze = encode_exp_z3 descr env e in
      let zp = encode_pattern_z3 descr env name p t in
      mk_ite_fast zp.t ze.t (encode_branches_aux_z3 descr env name bs t).t |> mk_term

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
    | VRecord _ -> failwith "Record in SMT encoding"

  let init_solver symbs =
    Var.reset () ;
    let env = { ctx = [];
                const_decls = ConstantSet.empty;
                type_decls = StringMap.empty;
                symbolics = VarMap.empty}
    in
    BatList.iter (fun (v,e) -> add_symbolic env v e) symbs;
    env

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

  let add_symbolic (env : smt_env) (b: Var.t list) (ety: Syntax.ty_or_exp) =
    match ety with
    | Ty ty ->
       (match ty with
       | TTuple ts ->
          BatList.iter2 (fun b ty ->
              env.symbolics <- VarMap.add b (Ty ty) env.symbolics) b ts
       | _ ->
          env.symbolics <- VarMap.add (BatList.hd b) ety env.symbolics)
    | Exp e ->
       (match e.e with
        | ETuple es ->
           BatList.iter2 (fun b e ->
               env.symbolics <- VarMap.add b (Exp e) env.symbolics) b es
        | _ ->
           env.symbolics <- VarMap.add (BatList.hd b) ety env.symbolics)

  let rec ty_to_sort (ty: ty) : sort =
    match ty with
    | TVar {contents= Link t} -> ty_to_sort t
    | TBool -> BoolSort
    | TInt _ -> IntSort
    | TTuple _
    | TOption _
    | TMap _ -> failwith "Not a single sort"
    (*       mk_array_sort ctx (ty_to_sort ctx ty1) (ty_to_sort ctx ty2)*)
    | TVar _ | QVar _ | TArrow _ | TRecord _ ->
       failwith
         (Printf.sprintf "internal error (ty_to_sort): %s"
            (Printing.ty_to_string ty))

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
    | TRecord _ -> failwith "Record type in SMT"
    | TVar _ | QVar _ | TArrow _ ->
      failwith
        (Printf.sprintf "internal error (ty_to_sort): %s"
           (Printing.ty_to_string ty))

  let create_vars (env: smt_env) descr (x: Syntax.var) =
    let name =
      if is_symbolic env.symbolics x then
        begin
          symbolic_var x
        end
      else create_name descr x
    in
    name

  let mk_constant =
    mk_constant

  let rec map3 f l1 l2 l3 =
    match (l1, l2, l3) with
      ([], [], []) -> []
    | (a1:: b1 :: c1 :: d1 :: e1 :: l1,
       a2:: b2 :: c2 :: d2 :: e2 :: l2,
       a3::b3:: c3 :: d3 :: e3 :: l3) ->
      let r1 = f a1 a2 a3 in
      let r2 = f b1 b2 b3 in
      let r3 = f c1 c2 c3 in
      let r4 = f d1 d2 d3 in
      let r5 = f e1 e2 e3 in
      r1 :: r2 :: r3 :: r4 :: r5 :: map3 f l1 l2 l3
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
    | EVal v when (match v.vty with | Some (TTuple _) -> true | _ -> false) ->
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
    | EFun _ | EApp _ ->
      failwith "function in smt encoding"
    | ERecord _ | EProject _ -> failwith "record in smt encoding"
    | _ ->
      (* Printf.printf "expr: %s\n" (Syntax.show_exp ~show_meta:false e); *)
      [encode_exp_z3_single descr env e]

  and encode_branches_z3 descr env names bs (t: ty) =
    match isEmptyBranch bs with
    | true -> failwith "internal error (encode_branches)"
    | false ->
      encode_branches_aux_z3 descr env names bs t

  (* I'm assuming here that the cases are exhaustive *)
  and encode_branches_aux_z3 descr env names bs (t: ty) =
    match popBranch bs with
    | ((p,e), bs) when isEmptyBranch bs ->
      let _ = encode_pattern_z3 descr env names p t in
      let zes = encode_exp_z3 descr env e in
      zes
    |  ((p,e), bs) ->
      let zes = encode_exp_z3 descr env e in
      let zps = encode_pattern_z3 descr env names p t in
      let guard = combine_term zps in
      lift2 (fun ze accze ->
          mk_ite_fast guard.t ze.t accze.t |>
          mk_term ~tloc:e.espan) zes
        (encode_branches_aux_z3 descr env names bs t)


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
      mk_term ~tloc:v.vspan ~tdescr:"val"
    | VOption _ -> failwith "options should have been unboxed"
    | VTuple _ -> failwith "internal error (check that tuples are flat)"
    | VClosure _ -> failwith "internal error (closure in smt)"
    | VMap map -> failwith "not doing maps yet"
    | VRecord _ -> failwith "Record in SMT encoding"

  let init_solver symbs =
    Var.reset () ;
    let env = { ctx = [];
                const_decls = ConstantSet.empty;
                type_decls = StringMap.empty;
                symbolics = VarMap.empty}
    in
    (* assumes symbs are not of type tuple here *)
    BatList.iter (fun (v,e) -> add_symbolic env [v] e) symbs;
    env

end
