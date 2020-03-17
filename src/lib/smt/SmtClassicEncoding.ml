open Nv_datastructures
open Nv_lang
open Syntax
open Collections
open SmtUtils
open SmtLang
open Nv_interpreter
open Nv_utils.OCamlUtils

module type ClassicEncodingSig = SmtEncodingSigs.Encoding with type network_type = Syntax.network
module ClassicEncoding (E: SmtEncodingSigs.ExprEncoding) : ClassicEncodingSig =
struct
  open E

  type network_type = Syntax.network

  let add_symbolic_constraints env requires sym_vars =
    (* Declare the symbolic variables: ignore the expression in case of SMT *)
    VarMap.iter
      (fun v e ->
         let names = create_vars env "" v in
         let sort = SmtUtils.ty_to_sort (Syntax.get_ty_from_tyexp e) in
         let symb = mk_constant env names sort
           ~cdescr:"Symbolic variable decl"
         in
           match sort with
             | IntSort ->
               SmtUtils.add_constraint env (mk_term (mk_leq (mk_int 0) symb.t))
             | _ -> ()
      ) sym_vars ;
    (* add the require clauses *)
    BatList.iter
      (fun e ->
         let es = encode_exp_z3 "" env e in
         ignore (lift1 (fun e -> SmtUtils.add_constraint env e) es)) requires

  let encode_z3_merge str env merge =
    let rec loop merge acc =
      match merge.e with
      | EFun {arg= x; argty= Some xty; body= exp; _} ->
        (match exp.e with
         | EFun _ ->
           loop exp ((x,xty) :: acc)
         | _ ->
           let xstr = BatList.rev_map (fun (x,xty) ->
               mk_constant env (create_vars env str x) (SmtUtils.ty_to_sort xty)
                 ~cdescr:"" ~cloc:merge.espan )
               ((x,xty) :: acc) in
           let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
           let results =
             lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
           let es = encode_exp_z3 str env exp in
           ignore(lift2 (fun e result ->
               SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t))) es results);
           (results, xstr))
      | _ -> failwith "internal error"
    in
    loop merge []

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
    | EFun {arg= x; argty= Some xty; body= exp; _} ->
      (match exp.e with
       | EFun _ ->
         encode_z3_trans_aux exp ((x,xty) :: acc)
       | _ ->
         (BatList.rev_map (fun (x, xty) ->
              (x, SmtUtils.ty_to_sort xty)) ((x, xty) :: acc), exp))
    | _ -> failwith "internal error"

  let encode_z3_trans trans =
    (* get edge argument*)
    let ex1,ex2,ex1ty,ex2ty,trans = match trans.e with
      | EFun {arg= ex1; argty= Some ex1ty; body= exp; _} ->
        (match exp.e with
         | EFun {arg= ex2; argty= Some ex2ty; body= exp; _} ->
           ex1,ex2,ex1ty,ex2ty,exp
         | _ -> failwith "Expected a function")
      | _ -> failwith "Expected a function"
    in
    let xs, exp = encode_z3_trans_aux trans [] in
    let expty = oget exp.ety in
    let expsorts = ty_to_sorts expty in
    (* construct new transfer function as a partial function of the edge*)
    let exp = aexp(efun (funcFull ex2 (Some ex2ty) (Some ex2ty) exp), Some (TArrow(ex2ty,expty)), exp.espan) in
    let exp = aexp(efun (funcFull ex1 (Some ex1ty) (Some ex1ty) exp), Some (TArrow(ex1ty,expty)), exp.espan) in
    fun edge str env ->
      let exp = InterpPartial.interp_partial_fun exp edge in
      (* Printf.printf "%s\n" (Printing.exp_to_string exp);
       * failwith "bla"; *)
      let xstr = BatList.map (fun (x,xsort) ->
          mk_constant env (create_vars env str x) xsort
            ~cdescr:"transfer x argument" ~cloc:trans.espan) xs
      in
      let names = create_strings (Printf.sprintf "%s-result" str) expty in
      let results =
        lift2 (mk_constant env) names expsorts in
      let es = encode_exp_z3 str env exp in
      ignore(lift2 (fun e result ->
          SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t))) es results);
      (results, xstr)

  let encode_z3_init str env e =
    (* Printf.printf "%s\n" (Printing.exp_to_string e); *)
    (* Printf.printf "%s\n" (Syntax.show_exp ~show_meta:false e); *)
    let names = create_strings (Printf.sprintf "%s-result" str) (oget e.ety) in
    let results =
      lift2 (mk_constant env) names (oget e.ety |> ty_to_sorts) in
    let es = encode_exp_z3 str env e in
    ignore(lift2 (fun e result ->
        SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t))) es results);
    results

  let encode_z3_assert str env _node assertion =
    let rec loop assertion acc =
      match assertion.e with
      | EFun {arg= x; argty= Some xty; body= exp; _} ->
        (match exp.e with
         | EFun _ ->
           loop exp ((x,xty) :: acc)
         | _ ->
           let xstr = BatList.rev_map (fun (x,xty) ->
               mk_constant env (create_vars env str x) (SmtUtils.ty_to_sort xty)
                 ~cdescr:"assert x argument" ~cloc:assertion.espan )
               ((x,xty) :: acc) in
           let names = create_strings (Printf.sprintf "%s-result" str) (oget exp.ety) in
           let results =
             lift2 (mk_constant env) names (oget exp.ety |> ty_to_sorts) in
           let es = encode_exp_z3 str env exp in
           ignore(lift2 (fun e result ->
               SmtUtils.add_constraint env (mk_term (mk_eq result.t e.t))) es results);
           (results, xstr))
      | _ -> failwith "internal error"
    in
    loop assertion []

  let encode_z3 (net: Syntax.network) : SmtUtils.smt_env =
    let env = init_solver net.symbolics ~labels:[] in
    let einit = net.init in
    let eassert = net.assertion in
    let emerge = net.merge in
    let etrans = net.trans in
    let nodes = (AdjGraph.nb_vertex net.graph) in
    let aty = net.attr_type in
    (* Map each edge to transfer function result *)

    (* incoming_map is a map from vertices to list of incoming edges *)
    (* let incoming_map = ref AdjGraph.VertexMap.empty in *)
    let incoming_map = Array.make nodes [] in
    (* trans_map maps each edge to the variable that holds the result *)
    let trans_map = ref AdjGraph.EdgeMap.empty in
    (* trans_input_map maps each edge to the incoming message variable *)
    let trans_input_map = ref AdjGraph.EdgeMap.empty in
    let enc_z3_trans = encode_z3_trans etrans in
    AdjGraph.iter_edges_e
      (fun (i, j) ->
         (* ( try
          *     let idxs = AdjGraph.VertexMap.find j !incoming_map in
          *     incoming_map :=
          *       AdjGraph.VertexMap.add j ((i, j) :: idxs) !incoming_map
          *   with _ ->
          *     incoming_map :=
          *       AdjGraph.VertexMap.add j [(i, j)] !incoming_map ) ; *)
         incoming_map.(j) <- (i,j) :: incoming_map.(j);
         let node_value n =
           avalue ((vnode n), Some Typing.node_ty, Span.default)
         in
         let edge =
           if SmtUtils.smt_config.unboxing then
             [node_value i; node_value j]
           else
             [avalue (vtuple [node_value i; node_value j],
                      Some (TTuple [TNode; TNode]), Span.default)]
         in
         (* Printf.printf "etrans:%s\n" (Printing.exp_to_string etrans); *)
         let trans, x =
           enc_z3_trans edge
             (Printf.sprintf "trans-%d-%d" i j)
             env
         in
         trans_input_map := AdjGraph.EdgeMap.add (i, j) x !trans_input_map ;
         trans_map := AdjGraph.EdgeMap.add (i, j) trans !trans_map )
      net.graph ;
    (*`Seutp labelling functions*)
    let attr_sort = ty_to_sorts aty in
    (* Compute the labelling as the merge of all inputs *)
    let labelling = Array.make nodes (of_list [])  in
    for i = 0 to nodes - 1 do
      (* compute each init attribute *)
      let node = avalue (vnode i, Some Typing.node_ty, Span.default) in
      let einit_i = Nv_interpreter.InterpPartial.interp_partial_fun einit [node] in
      let init = encode_z3_init (Printf.sprintf "init-%d" i) env einit_i in
      let in_edges = incoming_map.(i) in
      (* try AdjGraph.VertexMap.find i !incoming_map
       * with Not_found -> [] *)
      let emerge_i = InterpPartial.interp_partial_fun emerge [node] in
      (* Printf.printf "merge after interp:\n%s\n\n" (Printing.exp_to_string emerge_i);
       * failwith "bla"; *)
      let idx = ref 0 in
      let merged =
        BatList.fold_left
          (fun prev_result (x, y) ->
             incr idx ;
             let trans = AdjGraph.EdgeMap.find (x, y) !trans_map in
             let str = Printf.sprintf "merge-%d-%d" i !idx in
             let merge_result, x =
               encode_z3_merge str env emerge_i
             in
             let trans_list = to_list trans in
             let prev_result_list = to_list prev_result in
             BatList.iter2
               (fun y x -> SmtUtils.add_constraint env (mk_term (mk_eq y.t x.t)))
               (prev_result_list @ trans_list)
               x;
             merge_result
          )
          init in_edges
      in
      let lbl_i_name = SmtUtils.label_var i in
      let lbl_i = create_strings lbl_i_name aty in
      let lbl_iv = lift1 Nv_datastructures.Var.create lbl_i in
      add_symbolic env lbl_iv (Ty aty);
      let l = lift2 (fun lbl s -> mk_constant env (create_vars env "" lbl) s)
          lbl_iv attr_sort
      in
      ignore(lift2 (fun l merged ->
          SmtUtils.add_constraint env (mk_term (mk_eq l.t merged.t))) l merged);
      labelling.(i) <- l
    done ;
    (* Propagate labels across edges outputs *)
    AdjGraph.EdgeMap.iter
      (fun (i, _) x ->
         let label = labelling.(i) in
         BatList.iter2 (fun label x ->
             SmtUtils.add_constraint env (mk_term (mk_eq label.t x.t))) (to_list label) x)
      !trans_input_map ;
    (* add assertions at the end *)
    ( match eassert with
      | None -> ()
      | Some eassert ->
        let all_good = ref (mk_bool true) in
        for i = 0 to nodes - 1 do
          let label = labelling.(i) in
          let node = avalue (vnode i, Some Typing.node_ty, Span.default) in
          let eassert_i = InterpPartial.interp_partial_fun eassert [node] in
          let result, x =
            encode_z3_assert (SmtUtils.assert_var i) env i eassert_i
          in
          BatList.iter2 (fun x label ->
              SmtUtils.add_constraint env (mk_term (mk_eq x.t label.t))) x (to_list label);
          let assertion_holds =
            lift1 (fun result -> mk_eq result.t (mk_bool true) |> mk_term) result
            |> combine_term in
          all_good :=
            mk_and !all_good assertion_holds.t
        done ;
        SmtUtils.add_constraint env (mk_term (mk_not !all_good)));
    (* add the symbolic variable constraints *)
    add_symbolic_constraints env net.requires (env.symbolics (*@ sym_vars*));
    env
end
