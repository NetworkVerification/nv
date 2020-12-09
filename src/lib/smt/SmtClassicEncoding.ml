open Nv_datastructures
open Nv_lang
open Syntax
open Collections
open SmtUtils
open SmtLang
open Nv_interpreter
open Nv_utils.OCamlUtils
open Nv_kirigami
open Batteries
open SrpRemapping

module type ClassicEncodingSig =
  SmtEncodingSigs.Encoding
    with type network_type = Syntax.declarations
     and type part_network_type = Syntax.declaration_groups

module ClassicEncoding (E : SmtEncodingSigs.ExprEncoding) : ClassicEncodingSig = struct
  open E

  type network_type = Syntax.declarations
  type part_network_type = Syntax.declaration_groups

  let add_symbolic_constraints env requires sym_vars =
    (* Declare the symbolic variables: ignore the expression in case of SMT *)
    VarMap.iter
      (fun v e ->
        let names = create_vars env "" v in
        let sort = SmtUtils.ty_to_sort (Syntax.get_ty_from_tyexp e) in
        let symb = mk_constant env names sort ~cdescr:"Symbolic variable decl" in
        (* integers are set to be non-negative *)
        (match sort with
        | IntSort -> SmtUtils.add_constraint env (mk_term (mk_leq (mk_int 0) symb.t))
        | _ -> ())
      )
      sym_vars;
    (* add the require clauses *)
    BatList.iter
      (fun e ->
        (* print_endline ("Encoding symbolic exp: " ^ Printing.exp_to_string e); *)
        let es = encode_exp_z3 "" env e in
        ignore (lift1 (fun e -> SmtUtils.add_constraint env e) es))
      requires
  ;;

  let add_assertions env assertions count =
    match assertions with
    | [] -> ()
    | _ ->
      let assert_vars =
        List.map
          (fun eassert ->
            count := !count + 1;
            (* print_endline (Printing.exp_to_string eassert); *)
            let z3_assert = encode_exp_z3 "" env eassert |> to_list |> List.hd in
            let assert_var =
              mk_constant env (Printf.sprintf "assert-%d" !count) (ty_to_sort TBool)
            in
            SmtUtils.add_constraint env (mk_term (mk_eq assert_var.t z3_assert.t));
            assert_var)
          assertions
      in
      let all_good =
        List.fold_left
          (fun acc v -> mk_and acc v.t)
          (List.hd assert_vars).t
          (List.tl assert_vars)
      in
      SmtUtils.add_constraint env (mk_term (mk_not all_good))
        ;;

  let encode_z3_merge str env merge =
    let rec loop merge acc =
      match merge.e with
      | EFun { arg = x; argty = Some xty; body = exp; _ } ->
        (match exp.e with
        | EFun _ -> loop exp ((x, xty) :: acc)
        | _ ->
          let xstr =
            BatList.rev_map
              (fun (x, xty) ->
                mk_constant
                  env
                  (create_vars env str x)
                  (SmtUtils.ty_to_sort xty)
                  ~cdescr:""
                  ~cloc:merge.espan)
              ((x, xty) :: acc)
          in
          let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
          let results = lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
          let es = encode_exp_z3 str env exp in
          ignore
            (lift2
               (fun e result ->
                 SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
               es
               results);
          results, xstr)
      | _ -> failwith "internal error"
    in
    loop merge []
  ;;

  (* let encode_z3_trans str env trans =
   *   let rec loop trans acc =
   *     match trans.e with
   *     | EFun {arg= x; argty= Some xty; body= exp; _} ->
   *       (match exp.e with
   *        | EFun _ ->
   *          loop exp ((x,xty) :: acc)
   *        | _ ->
   *          let xstr = BatList.rev_map (fun (x,xty) ->
   *              mk_constant env (create_vars env str x) (SmtUtils.ty_to_sort xty)
   *                ~cdescr:"transfer x argument" ~cloc:trans.espan)
   *              ((x,xty) :: acc) in
   *          let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
   *          let results =
   *            lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
   *          let es = encode_exp_z3 str env exp in
   *          ignore(lift2 (fun e result ->
   *              SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t))) es results);
   *          (results, xstr))
   *     | _ -> failwith "internal error"
   *   in
   *   loop trans [] *)

  let rec encode_z3_trans_aux trans acc =
    match trans.e with
    | EFun { arg = x; argty = Some xty; body = exp; _ } ->
      (match exp.e with
      | EFun _ -> encode_z3_trans_aux exp ((x, xty) :: acc)
      | _ ->
        ( BatList.rev_map (fun (x, xty) -> x, SmtUtils.ty_to_sort xty) ((x, xty) :: acc)
        , exp ))
    | _ -> failwith "internal error"
  ;;

  let encode_z3_trans trans =
    (* get edge argument*)
    let ex1, ex2, ex1ty, ex2ty, trans =
      match trans.e with
      | EFun { arg = ex1; argty = Some ex1ty; body = exp; _ } ->
        (match exp.e with
        | EFun { arg = ex2; argty = Some ex2ty; body = exp; _ } ->
          ex1, ex2, ex1ty, ex2ty, exp
        | _ -> failwith "Expected a function")
      | _ -> failwith "Expected a function"
    in
    let xs, exp = encode_z3_trans_aux trans [] in
    let expty = oget exp.ety in
    let expsorts = ty_to_sorts expty in
    (* construct new transfer function as a partial function of the edge*)
    let exp =
      aexp
        ( efun (funcFull ex2 (Some ex2ty) (Some ex2ty) exp)
        , Some (TArrow (ex2ty, expty))
        , exp.espan )
    in
    let exp =
      aexp
        ( efun (funcFull ex1 (Some ex1ty) (Some ex1ty) exp)
        , Some (TArrow (ex1ty, expty))
        , exp.espan )
    in
    fun edge str env ->
      let exp = InterpPartial.interp_partial_fun exp edge in
      (* Printf.printf "%s\n" (Printing.exp_to_string exp);
       * failwith "bla"; *)
      let xstr =
        BatList.map
          (fun (x, xsort) ->
            mk_constant
              env
              (create_vars env str x)
              xsort
              ~cdescr:"transfer x argument"
              ~cloc:trans.espan)
          xs
      in
      let names = create_strings (Printf.sprintf "%s-result" str) expty in
      let results = lift2 (mk_constant env) names expsorts in
      let es = encode_exp_z3 str env exp in
      ignore
        (lift2
           (fun e result -> SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
           es
           results);
      results, xstr
  ;;

  let encode_z3_init str env e =
    (* Printf.printf "%s\n" (Printing.exp_to_string e); *)
    (* Printf.printf "%s\n" (Syntax.show_exp ~show_meta:false e); *)
    let names = create_strings (Printf.sprintf "%s-result" str) (oget e.ety) in
    let results = lift2 (mk_constant env) names (oget e.ety |> ty_to_sorts) in
    let es = encode_exp_z3 str env e in
    ignore
      (lift2
         (fun e result -> SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
         es
         results);
    results
  ;;

  (* Currently unused, but might be if we split up assertions *)
  let encode_z3_assert str env _node assertion =
    let rec loop assertion acc =
      match assertion.e with
      | EFun { arg = x; argty = Some xty; body = exp; _ } ->
        (match exp.e with
        | EFun _ -> loop exp ((x, xty) :: acc)
        | _ ->
          let xstr =
            BatList.rev_map
              (fun (x, xty) ->
                mk_constant
                  env
                  (create_vars env str x)
                  (SmtUtils.ty_to_sort xty)
                  ~cdescr:"assert x argument"
                  ~cloc:assertion.espan)
              ((x, xty) :: acc)
          in
          let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
          let results = lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
          let es = encode_exp_z3 str env exp in
          ignore
            (lift2
               (fun e result ->
                 SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
               es
               results);
          results, xstr)
      | _ -> failwith "internal error"
    in
    loop assertion []
  ;;

  (* get the arguments and internal expression for a given hypothesis predicate *)
  let rec encode_predicate_aux hyp acc =
    match hyp.e with
    | EFun { arg = x; argty = Some xty; body = exp; _ } ->
      (match exp.e with
      | EFun _ -> encode_predicate_aux exp ((x, xty) :: acc)
      | _ ->
        ( BatList.rev_map (fun (x, xty) -> x, SmtUtils.ty_to_sort xty) ((x, xty) :: acc)
        , exp ))
    | _ -> failwith "internal error"
  ;;

  let encode_predicate str env pred =
    let xs, exp = encode_predicate_aux pred [] in
    let expty = oget exp.ety in
    let expsorts = ty_to_sorts expty in
    let xstr =
      BatList.rev_map
        (fun (x, xsort) ->
          mk_constant
            env
            (create_vars env str x)
            xsort
            ~cdescr:"predicate x argument"
            ~cloc:pred.espan)
        xs
    in
    let names = create_strings (Printf.sprintf "%s-result" str) expty in
    let results = lift2 (mk_constant env) names expsorts in
    let es = encode_exp_z3 str env exp in
    (* can't add constraints yet, since we behave differently depending on what the predicate is for *)
    results, xstr, es
  ;;

  (* Encode the transfer of the given variable across the input/output
   * decomposed transfer function. *)
  let encode_kirigami_decomp str env optrans edge var =
    match optrans with
    | Some exp ->
      let enc_z3_trans = encode_z3_trans exp in
      let i, j = edge in
      let node_value n = avalue (vnode n, Some TNode, Span.default) in
      let edge = [node_value i; node_value j] in
      let trans, tx = enc_z3_trans edge (Printf.sprintf "trans-%s" str) env in
      BatList.iter2
        (fun e result -> SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t)))
        tx
        (to_list var);
      trans
    | None -> var

  (* let encode_z3_interface env aty labels interface partitioned_srp =
   *   (\* get edge argument*\)
   *   let ex1, ex2, ex1ty, ex2ty, interface =
   *     match interface.e with
   *     | EFun { arg = ex1; argty = Some ex1ty; body = exp; _ } ->
   *       (match exp.e with
   *       | EFun { arg = ex2; argty = Some ex2ty; body = exp; _ } ->
   *         ex1, ex2, ex1ty, ex2ty, exp
   *       | _ -> failwith "Expected a function")
   *     | _ -> failwith "Expected a function"
   *   in
   *   let get_pred edge =
   *     let p = InterpPartial.interp_partial_fun interface edge in
   *     match p.e with
   *     | ESome exp -> Some exp
   *     | EVal { v = VOption o; _ } ->
   *       (match o with
   *       | Some _ -> failwith "got a some value, which I didn't expect"
   *       | None -> None)
   *     | ETuple [{ e = EVal { v = VBool b; _ }; _ }; p] -> if b then Some p else None
   *     | _ -> failwith "got a non-option, which I didn't expect"
   *   in
   *   let node_value n = avalue (vnode n, Some Typing.node_ty, Span.default) in
   *   let edge_to_exps (i, j) =
   *     if SmtUtils.smt_config.unboxing
   *     then [node_value i; node_value j]
   *     else
   *       [ avalue
   *           ( vtuple [node_value i; node_value j]
   *           , Some (TTuple [TNode; TNode])
   *           , Span.default ) ]
   *   in
   *   let partitioned_srp =
   *     { partitioned_srp with
   *       inputs =
   *         AdjGraph.VertexMap.map
   *           (fun input_exps ->
   *             List.map
   *               (fun e -> { e with pred = get_pred (edge_to_exps e.edge) })
   *               input_exps)
   *           partitioned_srp.inputs
   *     ; outputs =
   *         AdjGraph.VertexMap.map
   *           (fun outputs ->
   *             List.map (fun (edge, _) -> edge, get_pred (edge_to_exps edge)) outputs)
   *           partitioned_srp.outputs
   *     }
   *   in
   *   (\* next part is a statement which returns Some fn or None *\)
   *   (\* want to get back that function *\)
   *   (\* TODO
   *    * - extract the interface function
   *    * - compute the predicate associated with each edge
   *    * - produce all the requirements for the hypotheses from other partitions
   *    *   (to be sorted into lesser and greater after)
   *    * - produce the constraints for the outputs' guarantees
   *    * - return a map for the inputs to each node, and a map for the outputs of each node
   *    *\)
   *   ()
   * ;; *)

  let find_input_symbolics (hyp_var : Var.t) aty =
    let names = create_strings ("symbolic-" ^ Var.name hyp_var) aty in
    (* let sorts = ty_to_sorts aty in
     * let const_default cname csort = { cname; csort; cdescr = ""; cloc = Span.default } in
     * lift2 (fun n s -> ConstantSet.find (const_default n s) env.const_decls) names sorts *)
    lift1 (fun s -> mk_term (mk_var s)) names
    ;;

  let encode_kirigami_solve
      env
      graph
      count
      { aty; var_names; init; trans; merge; decomp }
      { inputs; outputs }
    =
    let aty = oget aty in
    let einit, etrans, emerge = init, trans, merge in
    let nodes = AdjGraph.nb_vertex graph in
    (* Extract variable names from e, and split them up based on which node they
       belong to. In the end, label_vars.(i) is the list of attribute variables
       for node i *)
    let label_vars : var E.t array =
      let aty_len =
        match aty with
        | TTuple tys -> List.length tys
        | _ -> 1
      in
      match var_names.e with
      | ETuple es ->
        (* Sanity check *)
        (* assert (aty_len * nodes = List.length es); *)
        let varnames =
          List.map
            (fun e ->
              match e.e with
              | EVar x -> x
              | _ -> failwith "")
            es
        in
        varnames |> List.ntake aty_len |> Array.of_list |> Array.map of_list
      | EVar x ->
        (* Not sure if this can happen, but if it does it's in networks with only one node *)
        Array.map of_list @@ Array.make 1 [x]
      | _ -> failwith "internal error (encode_algebra)"
    in
    (* Map each edge to transfer function result *)

    (* incoming_map is a map from vertices to list of incoming edges *)
    let incoming_map = Array.make nodes [] in
    (* trans_map maps each edge to the variable that holds the result *)
    let trans_map = ref AdjGraph.EdgeMap.empty in
    (* trans_input_map maps each edge to the incoming message variable *)
    let trans_input_map = ref AdjGraph.EdgeMap.empty in
    let eintrans, eouttrans =
      match decomp with
      | Some (lt, rt) -> lt, rt
      | None -> Some etrans, None
    in
    (* construct the input constants *)
    let input_map =
      AdjGraph.VertexMap.map
        (fun inputs ->
          List.map
            (fun { edge; var } ->
              let i, j = edge in
              encode_kirigami_decomp
                (Printf.sprintf "input%d-%d-%d" count i j)
                env
                eintrans
                edge
                (* get the relevant variables *)
                (find_input_symbolics var aty))
            inputs)
        inputs
    in
    let enc_z3_trans = encode_z3_trans etrans in
    AdjGraph.iter_edges_e
      (fun (i, j) ->
        incoming_map.(j) <- (i, j) :: incoming_map.(j);
        let node_value n = avalue (vnode n, Some Typing.node_ty, Span.default) in
        let edge =
          if SmtUtils.smt_config.unboxing
          then [node_value i; node_value j]
          else
            [ avalue
                ( vtuple [node_value i; node_value j]
                , Some (TTuple [TNode; TNode])
                , Span.default ) ]
        in
        (* Printf.printf "etrans:%s\n" (Printing.exp_to_string etrans); *)
        let trans, x = enc_z3_trans edge (Printf.sprintf "trans%d-%d-%d" count i j) env in
        trans_input_map := AdjGraph.EdgeMap.add (i, j) x !trans_input_map;
        trans_map := AdjGraph.EdgeMap.add (i, j) trans !trans_map)
      graph;
    (* Setup labelling functions *)
    let attr_sort = ty_to_sorts aty in
    (* Compute the labelling as the merge of all inputs *)
    let labelling = Array.make nodes (of_list []) in
    for i = 0 to nodes - 1 do
      (* compute each init attribute *)
      let node = avalue (vnode i, Some Typing.node_ty, Span.default) in
      let einit_i = Nv_interpreter.InterpPartial.interp_partial_fun einit [node] in
      let init = encode_z3_init (Printf.sprintf "init%d-%d" count i) env einit_i in
      let in_edges = incoming_map.(i) in
      let emerge_i = InterpPartial.interp_partial_fun emerge [node] in
      (* Printf.printf "merge after interp:\n%s\n\n" (Printing.exp_to_string emerge_i);
       * failwith "bla"; *)
      let idx = ref 0 in
      let merged =
        BatList.fold_left
          (fun prev_result (x, y) ->
            incr idx;
            let trans = AdjGraph.EdgeMap.find (x, y) !trans_map in
            let str = Printf.sprintf "merge%d-%d-%d" count i !idx in
            let merge_result, x = encode_z3_merge str env emerge_i in
            let trans_list = to_list trans in
            let prev_result_list = to_list prev_result in
            BatList.iter2
              (fun y x -> SmtUtils.add_constraint env (mk_term (mk_eq y.t x.t)))
              (prev_result_list @ trans_list)
              x;
            merge_result)
          init
          in_edges
      in
      let merged =
        BatList.fold_left
          (fun prev_result input ->
            incr idx;
            let str = Printf.sprintf "merge-input%d-%d-%d" count i !idx in
            let merge_result, x = encode_z3_merge str env emerge_i in
            let input_list = to_list input in
            let prev_result_list = to_list prev_result in
            BatList.iter2
              (fun y x -> SmtUtils.add_constraint env (mk_term (mk_eq y.t x.t)))
              (prev_result_list @ input_list)
              x;
            merge_result)
          merged
          (AdjGraph.VertexMap.find i input_map)
      in
      let lbl_iv = label_vars.(i) in
      add_symbolic env lbl_iv (Ty aty);
      let l =
        lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s) lbl_iv attr_sort
      in
      ignore
        (lift2
           (fun l merged -> SmtUtils.add_constraint env (mk_term (mk_eq l.t merged.t)))
           l
           merged);
      labelling.(i) <- l
    done;
    (* construct the output constants *)
    (* TODO: add predicate constraints on outputs *)
    let _output_map =
      AdjGraph.VertexMap.mapi
        (fun v outputs ->
          List.map
            (fun ((i, j), _) ->
              encode_kirigami_decomp
                (Printf.sprintf "output%d-%d-%d" count i j)
                env
                eouttrans
                (i, j)
                labelling.(v))
            outputs)
        outputs
    in
    (* Propagate labels across edges outputs *)
    AdjGraph.EdgeMap.iter
      (fun (i, _) x ->
        let label = labelling.(i) in
        BatList.iter2
          (fun label x -> SmtUtils.add_constraint env (mk_term (mk_eq label.t x.t)))
          (to_list label)
          x)
      !trans_input_map
  ;;

  let encode_solve env graph count { aty; var_names; init; trans; merge } =
    let aty = oget aty in
    let einit, etrans, emerge = init, trans, merge in
    let nodes = AdjGraph.nb_vertex graph in
    (* Extract variable names from e, and split them up based on which node they
       belong to. In the end, label_vars.(i) is the list of attribute variables
       for node i *)
    let label_vars : var E.t array =
      let aty_len =
        match aty with
        | TTuple tys -> List.length tys
        | _ -> 1
      in
      match var_names.e with
      | ETuple es ->
        (* Sanity check *)
        (* assert (aty_len * nodes = List.length es); *)
        let varnames =
          List.map
            (fun e ->
              match e.e with
              | EVar x -> x
              | _ -> failwith "")
            es
        in
        varnames |> List.ntake aty_len |> Array.of_list |> Array.map of_list
      | EVar x ->
        (* Not sure if this can happen, but if it does it's in networks with only one node *)
        Array.map of_list @@ Array.make 1 [x]
      | _ -> failwith "internal error (encode_algebra)"
    in
    (* Map each edge to transfer function result *)

    (* incoming_map is a map from vertices to list of incoming edges *)
    let incoming_map = Array.make nodes [] in
    (* trans_map maps each edge to the variable that holds the result *)
    let trans_map = ref AdjGraph.EdgeMap.empty in
    (* trans_input_map maps each edge to the incoming message variable *)
    let trans_input_map = ref AdjGraph.EdgeMap.empty in
    let enc_z3_trans = encode_z3_trans etrans in
    AdjGraph.iter_edges_e
      (fun (i, j) ->
        incoming_map.(j) <- (i, j) :: incoming_map.(j);
        let node_value n = avalue (vnode n, Some Typing.node_ty, Span.default) in
        let edge =
          if SmtUtils.smt_config.unboxing
          then [node_value i; node_value j]
          else
            [ avalue
                ( vtuple [node_value i; node_value j]
                , Some (TTuple [TNode; TNode])
                , Span.default ) ]
        in
        (* Printf.printf "etrans:%s\n" (Printing.exp_to_string etrans); *)
        let trans, x = enc_z3_trans edge (Printf.sprintf "trans%d-%d-%d" count i j) env in
        trans_input_map := AdjGraph.EdgeMap.add (i, j) x !trans_input_map;
        trans_map := AdjGraph.EdgeMap.add (i, j) trans !trans_map)
      graph;
    (* Setup labelling functions *)
    let attr_sort = ty_to_sorts aty in
    (* Compute the labelling as the merge of all inputs *)
    let labelling = Array.make nodes (of_list []) in
    for i = 0 to nodes - 1 do
      (* compute each init attribute *)
      let node = avalue (vnode i, Some Typing.node_ty, Span.default) in
      let einit_i = Nv_interpreter.InterpPartial.interp_partial_fun einit [node] in
      let init = encode_z3_init (Printf.sprintf "init%d-%d" count i) env einit_i in
      let in_edges = incoming_map.(i) in
      let emerge_i = InterpPartial.interp_partial_fun emerge [node] in
      (* Printf.printf "merge after interp:\n%s\n\n" (Printing.exp_to_string emerge_i);
       * failwith "bla"; *)
      let idx = ref 0 in
      let merged =
        BatList.fold_left
          (fun prev_result (x, y) ->
            incr idx;
            let trans = AdjGraph.EdgeMap.find (x, y) !trans_map in
            let str = Printf.sprintf "merge%d-%d-%d" count i !idx in
            let merge_result, x = encode_z3_merge str env emerge_i in
            let trans_list = to_list trans in
            let prev_result_list = to_list prev_result in
            BatList.iter2
              (fun y x -> SmtUtils.add_constraint env (mk_term (mk_eq y.t x.t)))
              (prev_result_list @ trans_list)
              x;
            merge_result)
          init
          in_edges
      in
      let lbl_iv = label_vars.(i) in
      add_symbolic env lbl_iv (Ty aty);
      let l =
        lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s) lbl_iv attr_sort
      in
      ignore
        (lift2
           (fun l merged -> SmtUtils.add_constraint env (mk_term (mk_eq l.t merged.t)))
           l
           merged);
      labelling.(i) <- l
    done;
    (* Propagate labels across edges outputs *)
    AdjGraph.EdgeMap.iter
      (fun (i, _) x ->
        let label = labelling.(i) in
        BatList.iter2
          (fun label x -> SmtUtils.add_constraint env (mk_term (mk_eq label.t x.t)))
          (to_list label)
          x)
      !trans_input_map
  ;;

  let encode_z3 (decls : Syntax.declarations) : SmtUtils.smt_env =
    let symbolics = get_symbolics decls in
    let graph = get_graph decls |> oget in
    let solves = get_solves decls in
    let assertions = get_asserts decls |> List.map InterpPartial.interp_partial in
    let requires = get_requires decls in
    let env = init_solver symbolics ~labels:[] in
    List.iteri (encode_solve env graph) solves;
    (* add assertions at the end *)
    (match assertions with
    | [] -> ()
    | _ ->
      (* Encode every assertion as an expression and record the name of the
          corresponding smt variable *)
      let assert_vars =
        List.mapi
          (fun i eassert ->
            let z3_assert = encode_exp_z3 "" env eassert |> to_list |> List.hd in
            let assert_var =
              mk_constant env (Printf.sprintf "assert-%d" i) (ty_to_sort TBool)
            in
            SmtUtils.add_constraint env (mk_term (mk_eq assert_var.t z3_assert.t));
            assert_var)
          assertions
      in
      (* Expression representing the conjunction of the assertion variables *)
      let all_good =
        List.fold_left
          (fun acc v -> mk_and acc v.t)
          (List.hd assert_vars).t
          (List.tl assert_vars)
      in
      SmtUtils.add_constraint env (mk_term (mk_not all_good)));
    (* add any require clauses constraints *)
    add_symbolic_constraints env requires env.symbolics;
    env
  ;;

  let kirigami_encode_z3 (dgs : declaration_groups) : SmtUtils.smt_env =
    (* need to use a counter i, as add_assertions gets called for multiple lists *)
    let i = ref (-1) in
    let symbolics = (get_symbolics dgs.hyps) @ (get_symbolics dgs.base) in
    let graph = get_graph dgs.base |> oget in
    let solves = get_solves dgs.base in
    let simplify_assertion e =
      let etrue = Syntax.e_val (Syntax.vbool true) in
      let simplified = InterpPartialFull.interp_partial e in
      if Syntax.equal_exps ~cmp_meta:false etrue simplified then None else Some simplified
    in
    let g_assertions = get_asserts dgs.guar |> List.filter_map simplify_assertion in
    let p_assertions = get_asserts dgs.prop |> List.filter_map simplify_assertion in
    (* print_endline ("Assertions encoded: " ^ string_of_int (List.length (g_assertions @ p_assertions))); *)
    let requires = get_requires dgs.base in
    let lh_requires = get_requires dgs.lth in
    let gh_requires = get_requires dgs.gth in
    let env = init_solver symbolics ~labels:[] in
    List.iteri (encode_solve env graph) solves;
    (* these require constraints are always included *)
    add_symbolic_constraints env requires env.symbolics;
    add_symbolic_constraints env lh_requires VarMap.empty;
    (* ranked initial checks: test guarantees *)
    (* push *)
    if List.is_empty g_assertions
    then ()
    else (
      add_command env ~comdescr:"push" SmtLang.Push;
      add_assertions env g_assertions i;
      (* pop *)
      add_command env ~comdescr:"pop" SmtLang.Pop);
    (* safety checks: add other hypotheses, test properties *)
    add_symbolic_constraints env gh_requires VarMap.empty;
    add_assertions env p_assertions i;
    (* print_endline ("Final env.ctx length: " ^ string_of_int (List.length env.ctx)); *)
    env
  ;;
end
