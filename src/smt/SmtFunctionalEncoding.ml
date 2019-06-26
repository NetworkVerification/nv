open Syntax
open Collections
open SmtUtils
open SmtLang

(** * Alternative SMT encoding *)
module type FunctionalEncodingSig = SmtEncodingSigs.Encoding with type network_type = Syntax.srp_unfold
module FunctionalEncoding (E: SmtEncodingSigs.ExprEncoding) : FunctionalEncodingSig =
struct
  open E

  type network_type = Syntax.srp_unfold
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

  (** An alternative SMT encoding, where we build an NV expression for
      each label, partially evaluate it and then encode it *)
  let encode_z3 (srp: Syntax.srp_unfold) : smt_env =
    let labels =
      AdjGraph.VertexMap.fold (fun _ xs acc -> xs :: acc) srp.srp_labels [] |>
      BatList.concat
    in
    let env = init_solver srp.srp_symbolics ~labels:labels in
    let aty = srp.srp_attr in
    let nodes = (AdjGraph.num_vertices srp.srp_graph) in

    let smt_labels =
      AdjGraph.VertexMap.map
        (fun lblu ->
           let lblu_s = BatList.map (fun (var, _) -> symbolic_var var) lblu in
           lift2 (mk_constant env) (of_list lblu_s) (ty_to_sorts aty)) srp.srp_labels
    in
    (* Add appropriate SRP constraints*)
    AdjGraph.fold_vertices (fun u () ->
        let lblt = try AdjGraph.VertexMap.find u smt_labels
          with Not_found -> failwith "label variable not found"
        in
        let merged = try AdjGraph.VertexMap.find u srp.srp_constraints
          with Not_found -> failwith "constraints not found"
        in
        let merged =
          if smt_config.unboxing then
            begin
              let merged = InterpPartialFull.interp_partial merged in
              (* Printf.printf "merge after interp:\n%s\n" (Printing.exp_to_string merged);
               * failwith "merged"; *)
              merged
            end
          else
            merged
        in
        let str = Printf.sprintf "merge-%d" u in
        (* compute SMT encoding of label constraint*)
        let merged = encode_exp_z3 str env merged in
        ignore(lift2 (fun lblu merged ->
            add_constraint env (mk_term (mk_eq lblu.t merged.t))) lblt merged))
      nodes ();
    (* add assertions at the end *)
    (* TODO: same as other encoding make it a function *)
    ( match srp.srp_assertion with
      | None -> ()
      | Some eassert ->
        let all_good = ref (mk_bool true) in
        for i = 0 to nodes - 1 do
          let label =
            AdjGraph.VertexMap.find i smt_labels
          in
          let node = avalue (vint (Integer.of_int i), Some Typing.node_ty, Span.default) in
          let eassert_i = InterpPartial.interp_partial_fun eassert [node] in
          let result, x =
            encode_z3_assert (assert_var i) env (Integer.of_int i) eassert_i
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
    add_symbolic_constraints env srp.srp_requires env.symbolics;
    env
end
