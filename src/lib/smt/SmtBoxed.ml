open Nv_lang
open Nv_datastructures
open Nv_datatypes
open Nv_utils.PrimitiveCollections
open Syntax
open Collections
open SmtLang
open SmtUtils
open Nv_utils.OCamlUtils

module Boxed: SmtEncodingSigs.ExprEncoding =
struct

  type 'a t = 'a
  let lift1 f s = f s
  let lift2 f x y = f x y
  let combine_term t = t

  let create_strings str _ = str

  let create_vars env descr x =
    let name =
      if is_symbolic env.SmtUtils.symbolics x then
        begin
          let str = Var.to_string x in
          if BatString.starts_with str "label-" then
            str
          else
            "symbolic-" ^ str
        end
      else create_name descr x
    in
    name

  let to_list x = [x]

  let of_list x =
    BatList.hd x

  (** * Returns the SMT name of a datatype *)
  let rec datatype_name (ty : ty) : string option =
    match ty with
    | TVar {contents= Link t} -> datatype_name t
    | TTuple ts -> (
        match ts with
        | [] -> failwith "0-element tuples not allowed"
        | [_] -> failwith "1-element tuples not allowed"
        | ts ->
          let len = BatList.length ts in
          Some (Printf.sprintf "Pair%d" len))
    | TOption _ -> Some "Option"
    | TUnit -> Some "Unit"
    | _ -> None

  (** Returns the SMT name of any type *)
  let rec type_name (ty : ty) : string =
    match ty with
    | TVar {contents= Link t} -> type_name t
    | TTuple ts -> (
        match ts with
        | [] -> failwith "0-element tuples not allowed"
        | [_] -> failwith "1-element tuples not allowed"
        | ts ->
          let len = BatList.length ts in
          Printf.sprintf "Pair%d" len)
    | TOption _ -> "Option"
    | TUnit -> "Unit"
    | TBool -> "Bool"
    | TInt _ -> "Int"
    | TNode -> type_name (TInt 32)
    | TEdge -> type_name (TTuple [TNode; TNode])
    | TMap _ -> failwith "no maps yet"
    | TArrow _ | TVar _ | QVar _ | TRecord _ -> failwith "unsupported type in SMT"

  let rec ty_to_sort (ty: ty) : sort =
    match ty with
    | TVar {contents= Link t} -> ty_to_sort t
    | TUnit -> UnitSort
    | TBool -> BoolSort
    | TInt _ -> IntSort
    | TNode -> ty_to_sort (TInt 32)
    | TEdge -> ty_to_sort (TTuple [TNode; TNode])
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
    | TUnit ->
      let name = datatype_name ty |> oget in
      let constr = { constr_name = "mkUnit"; constr_args = [] } in
      { name; params = []; constructors = [constr] }
    | TNode | TInt _ | TBool -> failwith "not a datatype"
    | TEdge -> ty_to_type_decl (TTuple [TNode; TNode])
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
        if is_symbolic env.SmtUtils.symbolics x then
          begin
            (*symbolic_var x*)
            let str = Var.to_string x in
            if BatString.starts_with str "label-" then
              str
            else
              "symbolic-" ^ str
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
        | Syntax.Not, _ ->
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
        | Syntax.Eq, [e1;e2] ->
          let ze1 = encode_exp_z3 descr env e1 in
          let ze2 = encode_exp_z3 descr env e2 in
          mk_eq ze1.t ze2.t |>
          mk_term ~tloc:e.espan
        | Syntax.NLess, [e1;e2]
        | Syntax.ULess _, [e1;e2] ->
          let ze1 = encode_exp_z3 descr env e1 in
          let ze2 = encode_exp_z3 descr env e2 in
          mk_lt ze1.t ze2.t |>
          mk_term ~tloc:e.espan
        | Syntax.NLeq, [e1;e2]
        | Syntax.ULeq _, [e1;e2] ->
          let ze1 = encode_exp_z3 descr env e1 in
          let ze2 = encode_exp_z3 descr env e2 in
          mk_leq ze1.t ze2.t |>
          mk_term ~tloc:e.espan
        | Syntax.TGet _, _
        | Syntax.TSet _, _ -> failwith "TGet and TSet should be partially evaluated away"
        | Syntax.AtMost _, [_e1;_e2;_e3] -> failwith "not bothering with boxed version for now"
        | Syntax.MCreate, [_e1] ->
          failwith "not implemented"
        | Syntax.MGet, [_e1; _e2] ->
          failwith "not implemented"
        | Syntax.MSet, [_e1; _e2; _e3] ->
          failwith "not implemented"
        | MMap, [{e= EFun {arg= _x; argty= _ty1; resty= _ty2; body= _e1}; _}; _e2] ->
          failwith "not implemented yet"
        | MMapFilter, _
        | MMerge, _
        | MFoldNode, _
        | MFoldEdge, _
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
    | ETuple es ->
      let ty = oget e.ety in
      let pair_decl = compute_decl env ty |> oget in
      let pair_sort = ty_to_sort ty in
      let zes = BatList.map (fun e -> (encode_exp_z3 descr env e).t) es in
      let f = get_constructors pair_decl |> BatList.hd in
      mk_app (mk_constructor f.constr_name pair_sort) zes |>
      mk_term ~tloc:e.espan
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
    | ETy (e, _) -> encode_exp_z3 descr env e
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
    | PUnit, TUnit ->
      mk_bool true |>
      mk_term
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
                   | PVar _ -> mk_bool true |> mk_term
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
                  (fun _ t p ->  p, t ) ts ps
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
    | VUnit ->
      let unit_decl = compute_decl env TUnit in
      let f = (unit_decl |> oget |> get_constructors |> BatList.hd).constr_name in
      let e = mk_app (mk_constructor f (ty_to_sort TUnit)) [] in
      mk_term ~tloc:v.vspan e
    | VBool b ->
      mk_bool b |>
      mk_term ~tloc:v.vspan
    | VInt i ->
      mk_int_u32 i |>
      mk_term ~tloc:v.vspan
    | VNode n ->
      encode_value_z3 descr env @@
      avalue (vint (Integer.create ~size: 32 ~value:n), Some (TInt 32), v.vspan)
    | VEdge (n1, n2) ->
      let n1 = avalue (vnode n1, Some TNode, v.vspan) in
      let n2 = avalue (vnode n2, Some TNode, v.vspan) in
      encode_value_z3 descr env @@
      avalue (vtuple [n1; n2], Some (TTuple [TNode; TNode]), v.vspan)
    | VTuple vs -> (
        match oget v.vty with
        | TTuple _ ->
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
    | VMap _ -> failwith "not doing maps yet"
    | VRecord _ -> failwith "Record in SMT encoding"

  let init_solver symbs ~labels =
    Var.reset () ;
    let env = { ctx = [];
                const_decls = ConstantSet.empty;
                type_decls = StringMap.empty;
                symbolics = VarMap.empty}
    in
    BatList.iter (fun (v,e) -> add_symbolic env v e) symbs;
    BatList.iter (fun (v,ty) -> add_symbolic env v (Ty ty)) labels;
    env

end
