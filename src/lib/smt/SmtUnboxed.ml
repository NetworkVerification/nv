open Nv_datastructures
open Nv_lang
open Syntax
open Collections
open SmtLang
open SmtUtils
open Nv_utils.OCamlUtils

(** * SMT encoding without SMT-datatypes *)
module Unboxed : SmtEncodingSigs.ExprEncoding =
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

  let of_list x = x

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
    | TNode -> ty_to_sort (TInt 32)
    | TEdge
    | TTuple _
    | TMap _ -> failwith "Not a single sort"
    | TOption _
    | TUnit -> failwith "should be unboxed"
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
    | TNode -> ty_to_sorts (TInt 32)
    | TEdge ->  ty_to_sorts (TTuple [TNode; TNode])
    | TTuple ts -> (
        match ts with
        | [] -> failwith "empty tuple"
        | [t] -> ty_to_sorts t
        | ts -> BatList.map ty_to_sorts ts |> BatList.concat)
    | TOption _ -> failwith "options should be unboxed"
    | TUnit -> failwith "Unit shoulds be unboxed"
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
          let str = Var.to_string x in
          if BatString.starts_with str "label-" then
            str
          else
            "symbolic-" ^ str
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
        | Eq, [e1;e2] ->
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
        | MCreate, [_] ->
          failwith "not implemented"
        | MGet, [_; _] ->
          failwith "not implemented"
        | MSet, [_; _; _] ->
          failwith "not implemented"
        | MMap, [{e = EFun _}; _] ->
          (* | MMap, [{e= EFun {arg= x; argty= ty1; resty= ty2; body= e1}}; e2] -> *)
          failwith "not implemented yet"
        | MMapFilter, _
        | MMerge, _
        | MFoldNode, _
        | MFoldEdge, _
        | _ -> failwith "internal error (encode_exp_z3)")
    | ETy (e, _) -> encode_exp_z3_single descr env e
    | _ ->
      (* we always know this is going to be a singleton list *)
      let es = encode_exp_z3 descr env e in
      BatList.hd es

  and encode_exp_z3 descr env (e: exp) : term list =
    match e.e with
    | EOp (op, es) ->
      (match op, es with
       | Eq, [e1;e2] ->
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
    | ESome _ ->
      failwith "Some should be unboxed"
    | EMatch (e1, bs) ->
      let zes1 = encode_exp_z3 descr env e1 in
      (* intermediate variables no longer help here, probably
         because the expressions are pretty simple in this encoding *)
      encode_branches_z3 descr env zes1 bs (oget e1.ety)
    | ETy (e, _) -> encode_exp_z3 descr env e
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
    | VNode n ->
      encode_value_z3_single descr env @@
      avalue (vint (Integer.create ~size:32 ~value:n), Some (TInt 32), v.vspan)
    | VUnit -> failwith "units should have been unboxed"
    | VEdge _ -> failwith "edges should have been tupelized"
    | VOption _ -> failwith "options should have been unboxed"
    | VTuple _ -> failwith "internal error (check that tuples are flat)"
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
    (* assumes symbs are not of type tuple here. This is not a weird assumption
       to make. When unboxed, symbolics of type tuple are spread to multiple
       symbolic variables*)
    BatList.iter (fun (v,e) -> add_symbolic env [v] e) symbs;
    BatList.iter (fun (v,ty) -> add_symbolic env [v] (Ty ty)) labels;
    env

end
