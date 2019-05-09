(** * SMT encoding of network *)

open Collections
open Syntax
open Solution
open SolverUtil
open Profile
open SmtLang
open ExprEncodings
open SmtUtils

(* TODO:
   * make everything an smt_command. i.e. assert, declarations, etc.?
   * Make smt_term wrap around terms, print out more helpful
   comments, include location of ocaml source file
   * Have verbosity levels, we don't always need comments everywhere.
   * Don't hardcode tactics, try psmt (preliminary results were bad),
     consider par-and/par-or once we have multiple problems to solve.*)

(* Classic encodes the SRP as an SMT expression, Functional encodes
   the problem as an NV term which is then translated to SMT *)
type encoding_style = Classic | Functional

type smt_options =
  { mutable verbose        : bool;
    mutable optimize       : bool;
    mutable encoding       : encoding_style;
    mutable unboxing       : bool;
    mutable failures       : int option;
    mutable multiplicities : int Collections.StringMap.t
  }

let smt_config : smt_options =
  { verbose = false;
    optimize = false;
    encoding = Classic;
    unboxing = true;
    failures = None;
    multiplicities = Collections.StringMap.empty
  }

let get_requires_no_failures req =
  BatList.filter (fun e -> match e.e with
                        | EOp (AtMost _, _) -> false
                        | _ -> true) req

let get_requires_failures req =
  BatList.filter (fun e -> match e.e with
                        | EOp (AtMost _, _) -> true
                        | _ -> false) req
  |> List.hd

module type Encoding =
  sig
    val encode_z3: Syntax.network -> 'a list -> smt_env
  end

module ClassicEncoding (E: ExprEncoding): Encoding =
  struct
    open E

    let add_symbolic_constraints env requires sym_vars =
      (* Declare the symbolic variables: ignore the expression in case of SMT *)
      VarMap.iter
        (fun v e ->
          let names = create_vars env "" v in
          mk_constant env names (ty_to_sort (Syntax.get_ty_from_tyexp e))
                      ~cdescr:"Symbolic variable decl"
          |> ignore ) sym_vars ;
      (* add the require clauses *)
      BatList.iter
        (fun e ->
          let es = encode_exp_z3 "" env e in
          ignore (lift1 (fun e -> add_constraint env e) es)) requires


    let encode_z3_merge str env merge =
      let rec loop merge acc =
        match merge.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
           (match exp.e with
            | EFun _ ->
               loop exp ((x,xty) :: acc)
            | _ ->
               let xstr = BatList.rev_map (fun (x,xty) ->
                            mk_constant env (create_vars env str x) (ty_to_sort xty)
                                        ~cdescr:"" ~cloc:merge.espan )
                                        ((x,xty) :: acc) in
               let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
               let results =
                 lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
               let es = encode_exp_z3 str env exp in
               ignore(lift2 (fun e result ->
                          add_constraint env (mk_term (mk_eq result.t e.t))) es results);
               (results, xstr))
        | _ -> failwith "internal error"
      in
      loop merge []

    let encode_z3_trans str env trans =
      let rec loop trans acc =
        match trans.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
         (match exp.e with
          | EFun _ ->
             loop exp ((x,xty) :: acc)
          | _ ->
             let xstr = BatList.rev_map (fun (x,xty) ->
                          mk_constant env (create_vars env str x) (ty_to_sort xty)
                                      ~cdescr:"transfer x argument" ~cloc:trans.espan)
                                      ((x,xty) :: acc) in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results =
               lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
             let es = encode_exp_z3 str env exp in
             ignore(lift2 (fun e result ->
                        add_constraint env (mk_term (mk_eq result.t e.t))) es results);
             (results, xstr))
        | _ -> failwith "internal error"
      in
      loop trans []

    let encode_z3_init str env e =
      (* Printf.printf "%s\n" (Printing.exp_to_string e); *)
      (* Printf.printf "%s\n" (Syntax.show_exp ~show_meta:false e); *)
      let names = create_strings (Printf.sprintf "%s-result" str) (oget e.ety) in
      let results =
        lift2 (mk_constant env) names (oget e.ety |> ty_to_sorts) in
      let es = encode_exp_z3 str env e in
      ignore(lift2 (fun e result ->
                 add_constraint env (mk_term (mk_eq result.t e.t))) es results);
      results

    let encode_z3_assert str env node assertion =
      let rec loop assertion acc =
        match assertion.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
         (match exp.e with
          | EFun _ ->
             loop exp ((x,xty) :: acc)
          | _ ->
             let xstr = BatList.rev_map (fun (x,xty) ->
                            mk_constant env (create_vars env str x) (ty_to_sort xty)
                                        ~cdescr:"assert x argument" ~cloc:assertion.espan )
                                        ((x,xty) :: acc) in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results =
               lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
             let es = encode_exp_z3 str env exp in
             ignore(lift2 (fun e result ->
                        add_constraint env (mk_term (mk_eq result.t e.t))) es results);
             (results, xstr))
        | _ -> failwith "internal error"
      in
      loop assertion []

    let encode_z3 (net: Syntax.network) sym_vars : smt_env =
      let env = init_solver net.symbolics in
      let einit = net.init in
      let eassert = net.assertion in
      let emerge = net.merge in
      let etrans = net.trans in
      let nodes = (AdjGraph.num_vertices net.graph) in
      let edges = (AdjGraph.edges net.graph) in
      let aty = net.attr_type in
      (* map each node to the init result variable *)
      let init_map = ref AdjGraph.VertexMap.empty in
      for i = 0 to Integer.to_int nodes - 1 do
        let einit_i = Interp.interp_partial_fun einit [vint (Integer.of_int i)] in
        (* Printf.printf "%s\n" (Printing.exp_to_string einit); *)
        let init =
          encode_z3_init (Printf.sprintf "init-%d" i) env einit_i
        in
        (* add_constraint env (mk_term (mk_eq n.t (mk_int i))); *)
        init_map := AdjGraph.VertexMap.add (Integer.of_int i) init !init_map
      done ;

      (* Map each edge to transfer function result *)

      (* incoming_map is a map from vertices to list of incoming edges *)
      let incoming_map = ref AdjGraph.VertexMap.empty in
      (* trans_map maps each edge to the variable that holds the result *)
      let trans_map = ref AdjGraph.EdgeMap.empty in
      (* trans_input_map maps each edge to the incoming message variable *)
      let trans_input_map = ref AdjGraph.EdgeMap.empty in
      BatList.iter
        (fun (i, j) ->
          ( try
              let idxs = AdjGraph.VertexMap.find j !incoming_map in
              incoming_map :=
                AdjGraph.VertexMap.add j ((i, j) :: idxs) !incoming_map
            with _ ->
              incoming_map :=
                AdjGraph.VertexMap.add j [(i, j)] !incoming_map ) ;
          let edge =
            if smt_config.unboxing then
              [avalue ((vint i), Some Typing.node_ty, Span.default);
               avalue ((vint j), Some Typing.node_ty, Span.default)]
            else
              [avalue (vtuple [vint i; vint j],
                       Some Typing.edge_ty, Span.default)] in
          (* Printf.printf "etrans:%s\n" (Printing.exp_to_string etrans); *)
          let etrans_uv = Interp.interp_partial_fun etrans edge in
          let trans, x =
            encode_z3_trans
              (Printf.sprintf "trans-%d-%d" (Integer.to_int i)
                              (Integer.to_int j))
              env etrans_uv
          in
          trans_input_map := AdjGraph.EdgeMap.add (i, j) x !trans_input_map ;
          trans_map := AdjGraph.EdgeMap.add (i, j) trans !trans_map )
        edges ;

      (* Compute the labelling as the merge of all inputs *)
      let labelling = ref AdjGraph.VertexMap.empty in
      for i = 0 to Integer.to_int nodes - 1 do
        let init = AdjGraph.VertexMap.find (Integer.of_int i) !init_map in
        let in_edges =
          try AdjGraph.VertexMap.find (Integer.of_int i) !incoming_map
          with Not_found -> []
        in
        let node = avalue (vint (Integer.of_int i), Some Typing.node_ty, Span.default) in
        let emerge_i = Interp.interp_partial_fun emerge [node] in
        (* Printf.printf "emerge %d:%s\n" i (Printing.exp_to_string emerge_i); *)
        let idx = ref 0 in
        let merged =
          BatList.fold_left
            (fun acc (x, y) ->
              incr idx ;
              let trans = AdjGraph.EdgeMap.find (x, y) !trans_map in
              let str = Printf.sprintf "merge-%d-%d" i !idx in
              let merge_result, x =
                encode_z3_merge str env emerge_i
              in
              let trans_list = to_list trans in
              let acc_list = to_list acc in
              BatList.iter2 (fun y x ->
                  add_constraint env (mk_term (mk_eq y.t x.t))) (trans_list @ acc_list) x;
              merge_result )
            init in_edges
        in
        let lbl_i_name = label_var (Integer.of_int i) in
        let lbl_i = create_strings lbl_i_name aty in
        let lbl_iv = lift1 Var.create lbl_i in
        add_symbolic env lbl_iv aty;
        let l = lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s)
                      lbl_iv (ty_to_sorts aty)
        in

        ignore(lift2 (fun l merged ->
                   add_constraint env (mk_term (mk_eq l.t merged.t))) l merged);
        labelling := AdjGraph.VertexMap.add (Integer.of_int i) l !labelling
      done ;
      (* Propagate labels across edges outputs *)
      AdjGraph.EdgeMap.iter
        (fun (i, j) x ->
          let label = AdjGraph.VertexMap.find i !labelling in
          BatList.iter2 (fun label x ->
              add_constraint env (mk_term (mk_eq label.t x.t))) (to_list label) x)
        !trans_input_map ;
      (* add assertions at the end *)
      ( match eassert with
        | None -> ()
        | Some eassert ->
           let all_good = ref (mk_bool true) in
           for i = 0 to Integer.to_int nodes - 1 do
             let label =
               AdjGraph.VertexMap.find (Integer.of_int i) !labelling
             in
             let node = avalue (vint (Integer.of_int i), Some Typing.node_ty, Span.default) in
             let eassert_i = Interp.interp_partial_fun eassert [node] in
             let result, x =
               encode_z3_assert (assert_var (Integer.of_int i)) env (Integer.of_int i) eassert_i
             in
             BatList.iter2 (fun x label ->
                 add_constraint env (mk_term (mk_eq x.t label.t))) x (to_list label);
             let assertion_holds =
               lift1 (fun result -> mk_eq result.t (mk_bool true) |> mk_term) result
               |> combine_term in
             all_good :=
               mk_and !all_good assertion_holds.t
           done ;
           add_constraint env (mk_term (mk_not !all_good)));
      (* add the symbolic variable constraints *)
      add_symbolic_constraints env net.requires (env.symbolics (*@ sym_vars*));
      env
  end

(** * Alternative SMT encoding *)
module FunctionalEncoding (E: ExprEncoding) : Encoding =
  struct
    open E

    let add_symbolic_constraints env requires sym_vars =
      (* Declare the symbolic variables: ignore the expression in case of SMT *)
      VarMap.iter
        (fun v e ->
          let names = create_vars env "" v in
          mk_constant env names (ty_to_sort (Syntax.get_ty_from_tyexp e))
                      ~cdescr:"Symbolic variable decl"
          |> ignore ) sym_vars ;
      (* add the require clauses *)
      BatList.iter
        (fun e ->
          let es = encode_exp_z3 "" env e in
          ignore (lift1 (fun e -> add_constraint env e) es)) requires

 let encode_z3_assert str env node assertion =
      let rec loop assertion acc =
        match assertion.e with
        | EFun {arg= x; argty= Some xty; body= exp} ->
         (match exp.e with
          | EFun _ ->
             loop exp ((x,xty) :: acc)
          | _ ->
             let acc = BatList.rev acc in
             let xs = BatList.map (fun (x,xty) -> create_vars env str x) acc in
             let xstr = BatList.map (fun x -> mk_constant env x (ty_to_sort xty)
                                    ~cdescr:"assert x argument" ~cloc:assertion.espan ) xs
             in
             let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
             let results =
               lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
             let es = encode_exp_z3 str env exp in
             ignore(lift2 (fun e result ->
                        add_constraint env (mk_term (mk_eq result.t e.t))) es results);
             (results, xstr))
        | _ -> failwith "internal error"
      in
      loop assertion []

    let node_exp (u: Integer.t) : Syntax.exp =
      aexp(e_val (vint u), Some Typing.node_ty, Span.default)

    let edge_exp (u: Integer.t) (v: Integer.t) : Syntax.exp =
      aexp(e_val (vtuple [vint u; vint v]),
           Some Typing.edge_ty, Span.default)

    (** An alternative SMT encoding, where we build an NV expression for
   each label, partially evaluate it and then encode it *)
    let encode_z3 (net: Syntax.network) sym_vars : smt_env =
      let env = init_solver net.symbolics in
      let einit = net.init in
      let eassert = net.assertion in
      let emerge = net.merge in
      let etrans = net.trans in
      let nodes = (AdjGraph.num_vertices net.graph) in
      let edges = (AdjGraph.edges net.graph) in
      let aty = net.attr_type in
      (* Create a map from nodes to smt variables denoting the label of the node*)
      let labelling =
        AdjGraph.fold_vertices (fun u acc ->
            let lbl_u_name = label_var u in
            let lbl_u = create_strings lbl_u_name aty in
            let lblt =
              lift2 (mk_constant env) lbl_u (ty_to_sorts aty) in
            add_symbolic env (lift1 Var.create lbl_u) aty;
            AdjGraph.VertexMap.add u lblt acc)
                               nodes AdjGraph.VertexMap.empty
      in

      let init_exp u = eapp einit (node_exp u) in
      let trans_exp u v x = eapp (eapp etrans (edge_exp u v)) x in
      let merge_exp u x y = eapp (eapp (eapp emerge (node_exp u)) x) y in

      (* map from nodes to incoming messages*)
      let incoming_messages_map =
        BatList.fold_left (fun acc (u,v) ->
            let lblu = aexp (evar (label_var u |> Var.create), Some aty, Span.default) in
            let transuv = trans_exp u v lblu in
            AdjGraph.VertexMap.modify_def [] v (fun us -> transuv :: us) acc)
                       AdjGraph.VertexMap.empty edges
      in

      (* map from nodes to the merged messages *)
      let merged_messages_map =
        AdjGraph.fold_vertices (fun u acc ->
            let messages = AdjGraph.VertexMap.find_default [] u incoming_messages_map in
            let best = BatList.fold_left (fun accm m -> merge_exp u m accm)
                                      (init_exp u) messages
            in
            let str = Printf.sprintf "merge-%d" (Integer.to_int u) in
            let best_smt = Interp.Full.interp_partial best |> encode_exp_z3 str env in
            AdjGraph.VertexMap.add u best_smt acc) nodes AdjGraph.VertexMap.empty
      in

      AdjGraph.fold_vertices (fun u () ->
          let lblu = try AdjGraph.VertexMap.find u labelling
                     with Not_found -> failwith "label variable not found"
          in
          let merged = try AdjGraph.VertexMap.find u merged_messages_map
                       with Not_found -> failwith "merged variable not found"
          in
          ignore(lift2 (fun lblu merged ->
                     add_constraint env (mk_term (mk_eq lblu.t merged.t))) lblu merged))
                             nodes ();
      (* add assertions at the end *)
      (* TODO: same as other encoding make it a function *)
      ( match eassert with
        | None -> ()
        | Some eassert ->
      let all_good = ref (mk_bool true) in
      for i = 0 to Integer.to_int nodes - 1 do
        let label =
          AdjGraph.VertexMap.find (Integer.of_int i) labelling
        in
        let result, x =
          encode_z3_assert (assert_var (Integer.of_int i)) env (Integer.of_int i) eassert
        in
        BatList.iter2 (fun x label ->
            add_constraint env (mk_term (mk_eq x.t label.t))) x (to_list label);
        let assertion_holds =
          lift1 (fun result -> mk_eq result.t (mk_bool true) |> mk_term) result
          |> combine_term in
        all_good :=
          mk_and !all_good assertion_holds.t
      done ;
      add_constraint env (mk_term (mk_not !all_good)));
      (* add the symbolic variable constraints *)
      add_symbolic_constraints env net.requires (env.symbolics (*@ sym_vars*));
      env
  end

    (** ** SMT query optimization *)
let rec alpha_rename_smt_term (renaming: string StringMap.t)
          (valMap: smt_term StringMap.t) (tm: smt_term) =
      match tm with
      | Int _ | Bool _ | Constructor _ -> tm
      | And (tm1, tm2) ->
         And (alpha_rename_smt_term renaming valMap tm1,
              alpha_rename_smt_term renaming valMap tm2)
      | Or (tm1, tm2) ->
         Or (alpha_rename_smt_term renaming valMap tm1,
             alpha_rename_smt_term renaming valMap tm2)
      | Not tm1 ->
         Not (alpha_rename_smt_term renaming valMap tm1)
      | Add (tm1, tm2) ->
         Add (alpha_rename_smt_term renaming valMap tm1,
              alpha_rename_smt_term renaming valMap tm2)
      | Sub (tm1, tm2) ->
         Sub (alpha_rename_smt_term renaming valMap tm1,
              alpha_rename_smt_term renaming valMap tm2)
      | Eq (tm1, tm2) ->
         Eq (alpha_rename_smt_term renaming valMap tm1,
             alpha_rename_smt_term renaming valMap tm2)
      | Lt (tm1, tm2) ->
         Lt (alpha_rename_smt_term renaming valMap tm1,
             alpha_rename_smt_term renaming valMap tm2)
      | Leq (tm1, tm2) ->
         Leq (alpha_rename_smt_term renaming valMap tm1,
              alpha_rename_smt_term renaming valMap tm2)
      | Ite (tm1, tm2, tm3) ->
         Ite (alpha_rename_smt_term renaming valMap tm1,
              alpha_rename_smt_term renaming valMap tm2,
              alpha_rename_smt_term renaming valMap tm3)
      | AtMost (tm1, tm2, tm3) ->
         AtMost (BatList.map (alpha_rename_smt_term renaming valMap) tm1,
                 tm2,
                 alpha_rename_smt_term renaming valMap tm3)
      | Var s ->
         let sr = match StringMap.Exceptionless.find s renaming with
           | None -> s
           | Some x -> x
         in
         (match StringMap.Exceptionless.find sr valMap with
          | None -> Var sr
          | Some tmv -> tmv)
      | Bv _ -> failwith "not yet"
      | App (tm1, tms) ->
         App (alpha_rename_smt_term renaming valMap tm1,
              BatList.map (alpha_rename_smt_term renaming valMap) tms)

    let alpha_rename_term (renaming: string StringMap.t) valMap (tm: term) =
      {tm with t = alpha_rename_smt_term renaming valMap tm.t}

    (** Removes all variable equalities *)
    let propagate_eqs (env : smt_env) =
      let updateUnionFind eqSets s =
        try
          StringMap.find s eqSets, eqSets
        with Not_found ->
          let r = BatUref.uref s in
          r, StringMap.add s r eqSets
      in
      (* compute equality classes of variables and remove equalities between variables *)
      let (eqSets, valMap, new_ctx) = BatList.fold_left (fun (eqSets, valMap, acc) c ->
                                  match c.com with
                                  | Assert tm ->
                                     (match tm.t with
                                      | Eq (tm1, tm2) ->
                                         (match tm1, tm2 with
                                          | Var s1, Var s2 ->
                                             let r1, eqSets = updateUnionFind eqSets s1 in
                                             let r2, eqSets = updateUnionFind eqSets s2 in
                                             BatUref.unite r1 r2;
                                             (eqSets, valMap, acc)
                                          | Var s1, Int _ | Var s1, Bool _ ->
                                             let valMap = StringMap.add s1 tm2 valMap in
                                             (eqSets, valMap, acc)
                                          | _ -> (eqSets, valMap, c :: acc))
                                      | _ -> (eqSets, valMap, c :: acc))
                                  | _ -> (eqSets, valMap, c :: acc))
                                        (StringMap.empty, StringMap.empty, []) env.ctx
      in
      let renaming = StringMap.map (fun r -> BatUref.uget r) eqSets in
      let newValMap = StringMap.fold (fun s v acc ->
                          match StringMap.Exceptionless.find s renaming with
                          | None -> StringMap.add s v acc
                          | Some r -> StringMap.add r v acc) valMap StringMap.empty
      in
      (* apply the computed renaming *)
      env.ctx <- BatList.rev_map (fun c ->
                     match c.com with
                     | Assert tm ->
                        {c with com = Assert (alpha_rename_term renaming newValMap tm)}
                     | Eval tm ->
                        {c with com = Eval (alpha_rename_term renaming newValMap tm)}
                     | _  -> c) new_ctx;
      (* remove unnecessary declarations *)
      (* had to increase stack size to avoid overflow here..
         consider better implementations of this function*)
      env.const_decls <-
        ConstantSet.filter (fun cdecl ->
            if StringMap.mem cdecl.cname newValMap then false
            else
              begin
                try
                  let repr = StringMap.find cdecl.cname renaming in
                  if repr = cdecl.cname then true else false
                with Not_found ->
                  true
              end) env.const_decls;
      renaming, env

    type smt_result = Unsat | Unknown | Sat of Solution.t

    (** Emits the code that evaluates the model returned by Z3. *)
    let eval_model (symbolics: Syntax.ty_or_exp VarMap.t)
                   (num_nodes: Integer.t)
                   (eassert: Syntax.exp option)
                   (renaming: string StringMap.t) : command list =
      let var x = "Var:" ^ x in
      (* Compute eval statements for labels *)
      (* let labels = *)
      (*   AdjGraph.fold_vertices (fun u acc -> *)
      (*       let lblu = label_var u in *)
      (*       let tm = mk_var (StringMap.find_default lblu lblu renaming) |> mk_term in *)
      (*       let ev = mk_eval tm |> mk_command in *)
      (*       let ec = mk_echo ("\"" ^ (var lblu) ^ "\"") |> mk_command in *)
      (*       ec :: ev :: acc) num_nodes [(mk_echo ("\"end_of_model\"") |> mk_command)] in *)
      let base = [(mk_echo ("\"end_of_model\"") |> mk_command)] in
      (* Compute eval statements for assertions *)
      let assertions =
        match eassert with
        | None -> base
        | Some _ ->
           AdjGraph.fold_vertices (fun u acc ->
               let assu = (assert_var u) ^ "-result" in
               let tm = mk_var (StringMap.find_default assu assu renaming) |> mk_term in
               let ev = mk_eval tm |> mk_command in
               let ec = mk_echo ("\"" ^ (var assu) ^ "\"")
                        |> mk_command in
               ec :: ev :: acc) num_nodes base
      in
      (* Compute eval statements for symbolic variables *)
      let symbols =
        VarMap.fold (fun sv _ acc ->
            let sv = symbolic_var sv in
            let tm = mk_var (StringMap.find_default sv sv renaming) |> mk_term in
            let ev = mk_eval tm |> mk_command in
            let ec = mk_echo ("\"" ^ (var sv) ^ "\"") |> mk_command in
            ec :: ev :: acc) symbolics assertions in
      symbols

    let parse_val (s : string) : Syntax.value =
      let lexbuf = Lexing.from_string s
      in
      try SMTParser.smtlib SMTLexer.token lexbuf
      with exn ->
        begin
          let tok = Lexing.lexeme lexbuf in
          failwith (Printf.sprintf "failed to parse string %s on %s" s tok)
        end

    let translate_model (m : (string, string) BatMap.t) : Solution.t =
      BatMap.foldi (fun k v sol ->
          let nvval = parse_val v in
          match k with
          | k when BatString.starts_with k "label" ->
             {sol with labels= AdjGraph.VertexMap.add (node_of_label_var k) nvval sol.labels}
          | k when BatString.starts_with k "assert-" ->
             {sol with assertions=
                         match sol.assertions with
                         | None ->
                            Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                                         (nvval |> Syntax.bool_of_val |> oget)
                                                         AdjGraph.VertexMap.empty)
                         | Some m ->
                            Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                                         (nvval |> Syntax.bool_of_val |> oget) m)
             }
          | k ->
             {sol with symbolics= Collections.StringMap.add k nvval sol.symbolics}) m
                   {symbolics = StringMap.empty;
                    labels = AdjGraph.VertexMap.empty;
                    assertions= None}

    let box_vals (xs : (int * Syntax.value) list) =
      match xs with
      | [(_,v)] -> v
      | _ ->
         vtuple (BatList.sort (fun (x1,x2) (y1,y2) -> compare x1 y1) xs
                 |> BatList.map (fun (x,y) -> y))

    (* TODO: boxing for symbolic variables as well *)
    let translate_model_unboxed (m : (string, string) BatMap.t) : Solution.t =
      let (symbolics, labels, assertions) =
        BatMap.foldi (fun k v (symbolics, labels, assertions) ->
            let nvval = parse_val v in
            match k with
            | k when BatString.starts_with k "label" ->
               (match proj_of_var k with
                | None ->
                   ( symbolics,
                     AdjGraph.VertexMap.add (node_of_label_var k) [(0,nvval)] labels,
                     assertions )

                | Some i ->
                   ( symbolics,
                     AdjGraph.VertexMap.modify_def
                       [] (node_of_label_var k) (fun xs -> (i,nvval) :: xs) labels,
                     assertions ))
          | k when BatString.starts_with k "assert-" ->
             ( symbolics,
               labels,
               match assertions with
               | None ->
                  Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                               (nvval |> Syntax.bool_of_val |> oget)
                                               AdjGraph.VertexMap.empty)
               | Some m ->
                  Some (AdjGraph.VertexMap.add (node_of_assert_var k)
                                               (nvval |> Syntax.bool_of_val |> oget) m) )
          | k ->
             (Collections.StringMap.add k nvval symbolics, labels, assertions)) m
                     (StringMap.empty,AdjGraph.VertexMap.empty, None)
      in
      { symbolics = symbolics;
        labels = AdjGraph.VertexMap.map (box_vals) labels;
        assertions = assertions }

    (** ** Translate the environment to SMT-LIB2 *)

      (* TODO: For some reason this version of env_to_smt does not work correctly..
         maybe investigate at some point *)
    (* let env_to_smt ?(verbose=false) info (env : smt_env) = *)
      (* let buf = Buffer.create 8000000 in *)
      (* (\* Emit context *\) *)
      (* Buffer.add_string buf "(set-option :model_evaluator.completion true)"; *)
      (* List.iter (fun c -> Buffer.add_string buf (command_to_smt verbose info c)) env.ctx; *)
      (* ConstantSet.iter (fun c -> *)
      (*     Buffer.add_string buf (const_decl_to_smt ~verbose:verbose info c)) env.const_decls; *)
      (* Buffer.contents buf *)

    let env_to_smt ?(verbose=false) info (env : smt_env) =
      let context = BatList.rev_map (fun c -> command_to_smt verbose info c) env.ctx in
      let context = BatString.concat "\n" context in

      (* Emit constants *)
      let constants = ConstantSet.to_list env.const_decls in
      let constants =
        BatString.concat "\n"
                         (BatList.map (fun c -> const_decl_to_smt ~verbose:verbose info c)
                                   constants)
      in
      (* Emit type declarations *)
      let decls = StringMap.bindings env.type_decls in
      let decls = String.concat "\n"
                                (BatList.map (fun (_,typ) -> type_decl_to_smt typ) decls) in
      Printf.sprintf "(set-option :model_evaluator.completion true)
                          \n %s\n %s\n %s\n" decls constants context
    (* this new line is super important otherwise we don't get a reply
      from Z3.. not understanding why*)

    let check_sat info =
      Printf.sprintf "%s\n"
                     ((CheckSat |> mk_command) |> command_to_smt smt_config.verbose info)

    (* Emits the query to a file in the disk *)
    let printQuery (chan: out_channel Lazy.t) (msg: string) =
      let chan = Lazy.force chan in
      Printf.fprintf chan "%s\n%!" msg

    let expr_encoding smt_config =
      match smt_config.unboxing with
      | true -> (module Unboxed : ExprEncoding)
      | false -> (module Boxed : ExprEncoding)

    (* Asks the SMT solver to return a model and translates it to NV lang *)
    let ask_for_model query chan info env solver renaming net =
      (* build a counterexample based on the model provided by Z3 *)
      let num_nodes = AdjGraph.num_vertices net.graph in
      let eassert = net.assertion in
      let model = eval_model env.symbolics num_nodes eassert renaming in
      let model_question = commands_to_smt smt_config.verbose info model in
      ask_solver solver model_question;
      if query then
        printQuery chan model_question;
      let model = solver |> parse_model in
      (match model with
       | MODEL m ->
          if smt_config.unboxing then
            Sat (translate_model_unboxed m)
          else
            Sat (translate_model m)
       | OTHER s ->
          Printf.printf "%s\n" s;
          failwith "failed to parse a model"
       | _ -> failwith "failed to parse a model")


    (** Asks the smt solver whether the query was unsat or not
     and returns a model if it was sat.*)
    let get_sat query chan info env solver renaming net reply =
      ask_solver solver "(get-info :all-statistics)\n
                         (echo \"end stats\")\n";
      let rs = get_reply_until "end stats" solver in
      let rs =
        BatList.filter (fun s -> BatString.starts_with s " :time" ||
                                   BatString.starts_with s " :memory") rs
        |> String.concat "\n"
      in
      Printf.printf "Z3 stats:\n %s\n" rs;
      match reply with
      | UNSAT -> Unsat
      | SAT ->
         ask_for_model query chan info env solver renaming net
      | UNKNOWN ->
         Unknown
      | _ -> failwith "unexpected answer from solver\n"

    let refineModelMinimizeFailures (model: Solution.t) info query chan
                                    solve renaming env net =
      match (get_requires_failures net.requires).e with
      | EOp(AtMost n, [e1;e2;e3]) ->
         (match e1.e with
          | ETuple es ->
             Collections.StringMap.iter (fun fvar fval ->
                 match fval.v with
                 | VBool b ->
                    if b then
                      Printf.printf "Initial model failed: %s\n" fvar;
                 | _ -> failwith "This should be a boolean variable") model.symbolics;
             let mult = smt_config.multiplicities in
             let arg2 =
               aexp(etuple (BatList.map (fun evar ->
                                match evar.e with
                                | EVar fvar ->
                                   let n = Collections.StringMap.find (Var.name fvar)
                                             mult in
                                   (exp_of_value
                                      (avalue (vint (Integer.of_int n),
                                               Some (TInt 32),
                                               Span.default)))
                                | _ -> failwith "expected a variable") es),
                    e2.ety,
                    Span.default)
             in
             let new_req =
               aexp (eop (AtMost n) [e1; arg2;e3], Some TBool, Span.default) in
             let zes = Unboxed.encode_exp_z3 "" env new_req in
             let zes_smt =
               Unboxed.(to_list (lift1 (fun ze -> mk_assert ze |> mk_command) zes))
             in
             Some (commands_to_smt smt_config.verbose info zes_smt)
          | _ -> failwith "expected a tuple")
      | _ -> failwith "expected at most"

    (** Refines the first model returned by the solver by asking if
       the counter example still holds when failing only the single
       links *)
    (* TODO: Avoid using this until we have support for source nodes in min-cut *)
    let refineModelWithSingles (model : Solution.t) info query chan solve renaming _ ds =
      (* Find and separate the single link failures from the rest *)
      let (failed, notFailed) =
        Collections.StringMap.fold (fun fvar fval (accFailed, accNotFailed) ->
            match fval.v with
            | VBool b ->
               if b then
                 begin
                   let fmult = Collections.StringMap.find fvar smt_config.multiplicities in
                   if fmult > 1 then
                     (accFailed, fvar :: accNotFailed)
                   else
                     (fvar :: accFailed, accNotFailed)
                 end
               else (accFailed, fvar :: accNotFailed)
            | _ -> failwith "This should be a boolean variable") model.symbolics ([], [])
      in
      match failed with
      | [] -> None
      | _ ->
         let failed =
           BatList.map (fun fvar -> (mk_eq (mk_var fvar) (mk_bool true))
                                    |> mk_term |> mk_assert |> mk_command) failed
           |> commands_to_smt smt_config.verbose info
         in
         let notFailed =
           BatList.map (fun fvar -> (mk_eq (mk_var fvar) (mk_bool false))
                                    |> mk_term |> mk_assert |> mk_command) notFailed
           |> commands_to_smt smt_config.verbose info
         in
         Some (failed ^ notFailed)

    let refineModel (model : Solution.t) info query chan env solver renaming
                    (net : Syntax.network) =
        let refiner = refineModelMinimizeFailures in
        match refiner model info query chan solver renaming env net with
        | None ->
           (* Console.warning "Model was not refined\n"; *)
           Sat model (* no refinement can occur *)
        | Some q ->
           Console.warning "Refining the model...\n";
           let checkSat = CheckSat |> mk_command |> command_to_smt smt_config.verbose info in
           let q = Printf.sprintf "%s%s\n" q checkSat in
           if query then
             (printQuery chan q);
           ask_solver solver q;
           let reply = solver |> parse_reply in
           let isSat = get_sat query chan info env solver renaming net reply in
           (* if the second query was unsat, return the first counterexample *)
           match isSat with
           | Sat newModel ->
              Console.warning "Refined the model";
              isSat
           | _ -> Sat model

    let solve info query chan ?symbolic_vars ?(params=[]) net =
      let sym_vars =
        match symbolic_vars with None -> [] | Some ls -> ls
      in
      let module ExprEnc = (val expr_encoding smt_config) in
      let module Enc =
        (val (if smt_config.encoding = Classic then
                (module ClassicEncoding(ExprEnc) : Encoding)
              else
                (module FunctionalEncoding(ExprEnc) : Encoding)))
      in

      (* compute the encoding of the network *)
      let renaming, env =
        time_profile "Encoding network"
          (fun () -> let env = Enc.encode_z3 net sym_vars in
                     if smt_config.optimize then propagate_eqs env
                     else StringMap.empty, env)
      in
      (* compile the encoding to SMT-LIB *)
      let smt_encoding =
        time_profile "Compiling query"
          (fun () -> env_to_smt ~verbose:smt_config.verbose info env) in
      (* print query to a file if asked to *)
      if query then
        printQuery chan smt_encoding;
      (* Printf.printf "communicating with solver"; *)
      (* start communication with solver process *)
      let solver = start_solver params in
      ask_solver_blocking solver smt_encoding;
      match smt_config.failures with
      | None ->
         let q = check_sat info in
         if query then
           printQuery chan q;
         ask_solver solver q;
         let reply = solver |> parse_reply in
         get_sat query chan info env solver renaming net reply
      | Some k ->
         let q = check_sat info in
         if query then
           printQuery chan q;
         (* ask if it is satisfiable *)
         ask_solver solver q;
         let reply = solver |> parse_reply in
         (* check the reply *)
         let isSat = get_sat query chan info env solver renaming net reply in
         (* In order to minimize refinement iterations, once we get a
            counter-example we try to minimize it by only keeping failures
            on single links. If it works then we found an actual
            counterexample, otherwise we refine using the first
            counterexample. *)
         match isSat with
         | Unsat -> Unsat
         | Unknown -> Unknown
         | Sat model1 ->
            refineModel model1 info query chan env solver renaming net


module CheckProps =
  struct

    open Slicing

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
          let env = init_solver net.symbolics in
          Boxed.add_symbolic env checka_var net.attr_type;
          let checka =
            Boxed.lift2 (fun checka s -> mk_constant env (Boxed.create_vars env "" checka) s)
              checka_var (Boxed.ty_to_sorts net.attr_type)
            |> unbox
          in
          let mergeExpr = Hashtbl.find mergeTable (snd edge) in
          let trans, x =
            encode_z3_trans
              (Printf.sprintf "trans-%d-%d" (Integer.to_int (fst edge))
                 (Integer.to_int (snd edge)))
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
          Boxed.add_symbolic env merge_var net.attr_type;
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
                               [aexp(eop UEq [evar ospf_var; evar old_ospf_var],
                                     Some TBool,
                                     Span.default);
                               aexp(eop UEq [evar bgp_var; evar old_bgp_var],
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

  end
