open Syntax
open SolverUtil
open SmtLang
open SmtUtils
open Slicing
open Smt
module Boxed = SmtBoxed.Boxed

let encode_z3_merge str env e =
  match e.e with
  | EFun { arg= x
         ; argty= xty
         ; body= {e= EFun {arg= y; argty= yty; body= exp}} } ->
    let xstr =
      mk_constant env (create_name str x)
        (ty_to_sort (oget xty))
    in
    let ystr =
      mk_constant env (create_name str y)
        (ty_to_sort (oget yty))
    in
    let name = Printf.sprintf "%s-result" str in
    let result =
      mk_constant env name
        (oget exp.ety |> ty_to_sort)
    in
    let e = Boxed.encode_exp_z3 str env exp in
    add_constraint env (mk_term (mk_eq result.t ((Boxed.to_list e) |> List.hd).t));
    (result, xstr, ystr)
  | _ -> failwith "internal error (encode_z3_merge)"

let encode_z3_trans str env e =
  match e.e with
  | EFun
      {arg= x; argty= xty; body= exp} ->
    let xstr =
      mk_constant env (create_name str x)
        (ty_to_sort (oget xty))
    in
    let name = Printf.sprintf "%s-result" str in
    let result =
      mk_constant env name
        (oget exp.ety |> ty_to_sort)
    in
    let e = Boxed.encode_exp_z3 str env exp in
    add_constraint env (mk_term (mk_eq result.t ((Boxed.to_list e) |> List.hd).t));
    (result, xstr)
  | _ -> failwith "internal error"

let checkMonotonicity info query chan net =
  let checka = Boxed.create_strings "checka" net.attr_type in
  let checka_var = Boxed.lift1 Var.create checka in
  let transTable = partialEvalOverEdges (AdjGraph.edges net.graph) net.trans in
  let mergeTable = partialEvalOverNodes (AdjGraph.num_vertices net.graph) net.merge in
  let solver = start_solver [] in
  let unbox x = Boxed.to_list x |> List.hd in
  Hashtbl.iter (fun edge trans ->
      let env = Boxed.init_solver net.symbolics [] in
      Boxed.add_symbolic env checka_var (Ty net.attr_type);
      let checka =
        Boxed.lift2 (fun checka s -> mk_constant env (Boxed.create_vars env "" checka) s)
          checka_var (Boxed.ty_to_sorts net.attr_type)
        |> unbox
      in
      let mergeExpr = Hashtbl.find mergeTable (snd edge) in
      let trans, x =
        encode_z3_trans
          (Printf.sprintf "trans-%d-%d" (fst edge)
             (snd edge))
          env trans
      in
      (* add transfer function constraints *)
      add_constraint env (mk_term (mk_eq checka.t x.t));
      let merge_result, x, y =
        encode_z3_merge "merge" env mergeExpr
      in
      (* add merge constraints *)
      add_constraint env (mk_term (mk_eq x.t checka.t));
      add_constraint env (mk_term (mk_eq y.t trans.t));
      let merge_nv = Boxed.create_strings "merge" net.attr_type in
      let merge_var = Boxed.lift1 Var.create merge_nv in
      let merge_smt =
        Boxed.lift2 (fun merge s -> mk_constant env (Boxed.create_vars env "" merge) s)
          merge_var (Boxed.ty_to_sorts net.attr_type)
        |> unbox
      in
      Boxed.add_symbolic env merge_var (Ty net.attr_type);
      (* merge result is equal to some nv variable *)
      add_constraint env (mk_term (mk_eq merge_smt.t merge_result.t));
      let old_ospf_var = Var.create "o" in
      let old_bgp_var = Var.create "b" in
      let ospf_var = Var.create "onew" in
      let bgp_var = Var.create "bnew" in
      (* encode the property in NV *)
      let property_exp =
        aexp(ematch (aexp(evar (unbox merge_var), Some net.attr_type, Span.default))
               (addBranch (PTuple [PWild; PWild; PVar ospf_var; PVar bgp_var; PWild])
                  (aexp (eop And
                           [aexp(eop Eq [evar ospf_var; evar old_ospf_var],
                                 Some TBool,
                                 Span.default);
                            aexp(eop Eq [evar bgp_var; evar old_bgp_var],
                                 Some TBool,
                                 Span.default)],
                         Some TBool, Span.default)) emptyBranch),
             Some TBool, Span.default)
      in
      let property =
        aexp(ematch (aexp (evar (unbox checka_var), Some net.attr_type, Span.default))
               (addBranch
                  (PTuple [PWild; PWild; PVar old_ospf_var; PVar old_bgp_var; PWild])
                  property_exp emptyBranch),
             Some TBool, Span.default)
      in
      let check = Boxed.encode_exp_z3 "" env property
      in
      let check_holds =
        Boxed.lift1 (fun check -> mk_eq check.t (mk_bool true) |> mk_term) check
        |> Boxed.combine_term
      in
      (* check negation *)
      add_constraint env (mk_term (mk_not check_holds.t));
      ask_solver_blocking solver ("(push)\n");
      if query then
        printQuery chan "(push)\n";
      let smt_q = env_to_smt info env in
      ask_solver_blocking solver smt_q;
      if query then
        printQuery chan smt_q;
      let q = check_sat info in
      ask_solver solver q;
      if query then
        printQuery chan q;
      let reply = solver |> parse_reply in
      ask_solver_blocking solver "(pop)\n";
      if query then
        printQuery chan "(pop)\n";
      match reply with
      | SAT ->
        Console.warning (Printf.sprintf "Policy on edge %s is non-monotonic"
                           (AdjGraph.printEdge edge))
      | UNSAT -> ()
      | _ -> failwith "unknown answer") transTable
