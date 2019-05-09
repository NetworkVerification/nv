(** * SMT encoding of network *)

open Collections
open Syntax
open Solution
open SolverUtil
open Profile
open SmtLang
open ExprEncodings
open SmtUtils
open SmtEncodings
open SmtOptimizations

(* TODO:
   * make everything an smt_command. i.e. assert, declarations, etc.?
   * Make smt_term wrap around terms, print out more helpful
   comments, include location of ocaml source file
   * Have verbosity levels, we don't always need comments everywhere.
   * Don't hardcode tactics, try psmt (preliminary results were bad),
     consider par-and/par-or once we have multiple problems to solve.*)

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
