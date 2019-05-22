open Collections
open Syntax
open SmtLang
open SmtExprEncodings
open SmtUtils

module type Encoding =
sig
  val encode_z3: Syntax.network -> 'a list -> smt_env
 val add_symbolic_constraints: smt_env ->  Syntax.exp list -> Syntax.ty_or_exp Collections.VarMap.t -> unit
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
      add_symbolic env lbl_iv (Ty aty);
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
    
  let edge_exp (u: Integer.t) (v: Integer.t) : Syntax.exp list =
    if smt_config.unboxing then
      [aexp (e_val (vint u), Some Typing.node_ty, Span.default);
       aexp (e_val (vint v), Some Typing.node_ty, Span.default)]
    else
      [aexp(e_val (vtuple [vint u; vint v]),  Some Typing.edge_ty, Span.default)]
    
  let init_exp einit u =
    Interp.Full.interp_partial_fun einit [node_exp u]

  (* Reduces the transfer function, maybe a full reduction is not
     necessary at this point, experiment to see if just reducing based
     on the edge is better *)
  let trans_exp etrans u v xs =
    let args = (edge_exp u v) @ xs in
    (Interp.Full.interp_partial_fun etrans args) |> Tnf.tnf_exp

  let merge_exp emerge u xs ys =
    let args = (node_exp u) :: (xs @ ys) in
    (Interp.Full.interp_partial_fun emerge args) |> Tnf.tnf_exp
    
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
    (* Create a map from nodes to variables and smt variables denoting
       the label of the node*)
    let labelling =
      AdjGraph.fold_vertices (fun u acc ->
          (* the string name that corresponds to the label of node u*)
          let lbl_u_name = label_var u in
          (*create one or more string names depending on boxed/unboxed encoding*)
          let lbl_u = create_strings lbl_u_name aty in
          (* create SMT variables *)
          let lblt = lift2 (mk_constant env) lbl_u (ty_to_sorts aty) in
          (*create label vars *)
          let lbl_vars =  lift1 Var.create lbl_u in 
          (* declare the label variable as a symbolic variable *)
          add_symbolic env lbl_vars (Ty aty); 
          AdjGraph.VertexMap.add u (lbl_vars, lblt) acc)
        nodes AdjGraph.VertexMap.empty
    in
    
    (* Map from nodes to incoming messages*)
    let incoming_messages_map =
      BatList.fold_left (fun acc (u,v) ->
          (* Find the label variables associated with node u*)
          let varu = fst (AdjGraph.VertexMap.find u labelling) in 
          let lblu =
            BatList.map (fun v ->
                (*find the type of each variable *)
                let tyu = get_ty_from_tyexp (Collections.VarMap.find v env.symbolics) in 
                aexp (evar v, Some tyu, Span.default)) (to_list varu)
          in
          (*compute the incoming message through the transfer function *)
          let transuv =  trans_exp etrans u v lblu in 
          (* add them to the incoming messages of node v *)
          AdjGraph.VertexMap.modify_def [] v (fun us -> transuv :: us) acc)
        AdjGraph.VertexMap.empty edges
    in

    (* map from nodes to the merged messages *)
    let merged_messages_map =
      AdjGraph.fold_vertices (fun u acc ->
          let messages = AdjGraph.VertexMap.find_default [] u incoming_messages_map in
          let best = BatList.fold_left (fun accm m -> merge_exp emerge u m accm)
              (init_exp einit u) messages
          in
          let str = Printf.sprintf "merge-%d" (Integer.to_int u) in
          let best_eval = Interp.Full.interp_partial best in
          Printf.printf "merged:%s\n" (Printing.exp_to_string best_eval);
          let best_smt = encode_exp_z3 str env best_eval in
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
