open Nv_lang
open Nv_lang.Collections
open Nv_lang.Syntax
open Nv_solution.Solution
open Nv_datastructures
open SmtUtils
open SmtLang
open SolverUtil

let prefix_if_needed varname =
  if
    BatString.starts_with varname "label-" ||
    BatString.starts_with varname "merge-" ||
    BatString.starts_with varname "trans-" ||
    BatString.starts_with varname "init-"  ||
    BatString.starts_with varname "assert-"
  then
    varname
  else
    "symbolic-" ^ varname
;;

(** Emits the code that evaluates the model returned by Z3. *)
let eval_model (symbolics: Syntax.ty_or_exp VarMap.t)
    (num_nodes: int)
    (eassert: Syntax.exp option)
    (renaming: string StringMap.t * smt_term StringMap.t) : command list =
  let renaming, valMap = renaming in
  let var x = "Var:" ^ x in
  let find_renamed_term str =
    let renamed = StringMap.find_default str str renaming in
    let smt_term =
      match StringMap.Exceptionless.find renamed valMap with
      | None -> mk_var renamed
      | Some tmv -> tmv
    in
    mk_term smt_term
  in
  (* Compute eval statements for labels *)
  (* let labels = *)
  (*   AdjGraph.fold_vertices (fun u acc -> *)
  (*       let lblu = label_var u in *)
  (*       let tm = mk_var (StringMap.find_default lblu lblu renaming) |> mk_term in *)
  (*       let ev = mk_eval tm |> mk_command in *)
  (*       let ec = mk_echo ("\"" ^ (var lblu) ^ "\"") |> mk_command in *)
  (*       ec :: ev :: acc) num_nodes [(mk_echo ("\"end_of_model\"") |> mk_command)] in *)
  let base = [(mk_echo ("\"end_of_model\"") |> mk_command)] in
  (* StringMap.iter (fun k v -> Printf.printf "(%s, %s)" k v) renaming; *)
  (* Compute eval statements for assertions *)
  let assertions =
    match eassert with
    | None -> base
    | Some _ ->
      AdjGraph.fold_vertices (fun u acc ->
          let assu = (SmtUtils.assert_var u) ^ "-result" in
          let tm = find_renamed_term assu in
          let ev = mk_eval tm |> mk_command in
          let ec = mk_echo ("\"" ^ (var assu) ^ "\"")
                   |> mk_command in
          ec :: ev :: acc) num_nodes base
  in
  (* Compute eval statements for symbolic variables *)
  let symbols =
    VarMap.fold (fun sv _ acc ->
        let sv = SmtUtils.symbolic_var sv in
        let z3name = prefix_if_needed sv in
        let tm = find_renamed_term z3name in
        let ev = mk_eval tm |> mk_command in
        let ec = mk_echo ("\"" ^ (var sv) ^ "\"") |> mk_command in
        ec :: ev :: acc) symbolics assertions in
  symbols

let rec parse_model (solver: solver_proc) =
  let rs = get_reply_until "end_of_model" solver in
  let rec loop rs model =
    match rs with
    | [] -> MODEL model
    | [v] when v = "end_of_model" ->  MODEL model
    | vname :: rs when (BatString.starts_with vname "Var:") ->
      let vname = BatString.lchop ~n:4 vname in
      let rec grab_vals rs acc =
        match rs with
        | [] -> failwith "expected string"
        | v :: _ when (BatString.starts_with v "Var:") || v = "end_of_model" ->
          (acc, rs)
        | v :: rs' ->
          grab_vals rs' (acc ^ v)
      in
      let vval, rs' = grab_vals rs "" in
      loop rs' (BatMap.add vname vval model)
    | _ ->
      failwith "wrong format"
  in loop rs BatMap.empty

let parse_val (s : string) : Syntax.value =
  let lexbuf = Lexing.from_string s
  in
  try SMTParser.smtlib SMTLexer.token lexbuf
  with _exn ->
    begin
      let tok = Lexing.lexeme lexbuf in
      failwith (Printf.sprintf "failed to parse string %s on %s" s tok)
    end

let translate_model (m : (string, string) BatMap.t) : Nv_solution.Solution.t =
  BatMap.foldi (fun k v sol ->
      let nvval = parse_val v in
      match k with
      | k when BatString.starts_with k "label" ->
        {sol with labels= AdjGraph.VertexMap.add (SmtUtils.node_of_label_var k) nvval sol.labels}
      | k when BatString.starts_with k "assert-" ->
        {sol with assertions=
                    match sol.assertions with
                    | None ->
                      Some (AdjGraph.VertexMap.add (SmtUtils.node_of_assert_var k)
                              (nvval |> Syntax.bool_of_val |> Nv_utils.OCamlUtils.oget)
                              AdjGraph.VertexMap.empty)
                    | Some m ->
                      Some (AdjGraph.VertexMap.add (SmtUtils.node_of_assert_var k)
                              (nvval |> Syntax.bool_of_val |> Nv_utils.OCamlUtils.oget) m)
        }
      | k ->
        let k_var = Var.of_var_string k in
        {sol with symbolics= VarMap.add k_var nvval sol.symbolics}) m
    {symbolics = VarMap.empty;
     labels = AdjGraph.VertexMap.empty;
     assertions= None;
     mask = None}

let box_vals (xs : (int * Syntax.value) list) =
  match xs with
  | [(_,v)] -> v
  | _ ->
    vtuple (BatList.sort (fun (x1,_x2) (y1,_y2) -> compare x1 y1) xs
            |> BatList.map (fun (_,y) -> y))

let translate_model_unboxed (m : (string, string) BatMap.t) : Nv_solution.Solution.t =
  let (symbolics, labels, assertions) =
    BatMap.foldi (fun k v (symbolics, labels, assertions) ->
        let nvval = parse_val v in
        match k with
        | k when BatString.starts_with k "label" ->
          (match SmtUtils.proj_of_var k with
           | None ->
             ( symbolics,
               AdjGraph.VertexMap.add (SmtUtils.node_of_label_var k) [(0,nvval)] labels,
               assertions )
           | Some i ->
             ( symbolics,
               AdjGraph.VertexMap.modify_def
                 [] (SmtUtils.node_of_label_var k) (fun xs -> (i,nvval) :: xs) labels,
               assertions ))
        | k when BatString.starts_with k "assert-" ->
          ( symbolics,
            labels,
            match assertions with
            | None ->
              Some (AdjGraph.VertexMap.add (SmtUtils.node_of_assert_var k)
                      (nvval |> Syntax.bool_of_val |> Nv_utils.OCamlUtils.oget)
                      AdjGraph.VertexMap.empty)
            | Some m ->
              Some (AdjGraph.VertexMap.add (SmtUtils.node_of_assert_var k)
                      (nvval |> Syntax.bool_of_val |> Nv_utils.OCamlUtils.oget) m) )
        | k ->
          ( let new_symbolics = VarMap.add (Var.of_var_string k) nvval symbolics in
            new_symbolics, labels, assertions )
      ) m (VarMap.empty,AdjGraph.VertexMap.empty, None)
  in
  { symbolics = symbolics;
    labels = AdjGraph.VertexMap.map box_vals labels;
    assertions = assertions;
    mask = None; }


(* Model Refiners *)
let refineModelMinimizeFailures (model: Nv_solution.Solution.t) info _query _chan
    _solve _renaming env requires =
  match (SmtUtils.get_requires_failures requires).e with
  | Syntax.EOp(Syntax.AtMost n, [e1;e2;e3]) ->
    (match e1.e with
     | ETuple es ->
       VarMap.iter (fun fvar fval ->
           match fval.v with
           | VBool b ->
             if b then
               Printf.printf "Initial model failed: %s\n" (Var.to_string fvar);
           | _ -> failwith "This should be a boolean variable") model.symbolics;
       let mult = SmtUtils.smt_config.SmtUtils.multiplicities in
       let arg2 =
         aexp(etuple (BatList.map (fun evar ->
             match evar.e with
             | EVar fvar ->
               let n = StringMap.find (Var.name fvar)
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
         aexp (eop (Syntax.AtMost n) [e1; arg2;e3], Some TBool, Span.default) in
       let zes = SmtUnboxed.Unboxed.encode_exp_z3 "" env new_req in
       let zes_smt =
         SmtUnboxed.Unboxed.(to_list (lift1 (fun ze -> mk_assert ze |> mk_command) zes))
       in
       Some (commands_to_smt SmtUtils.smt_config.SmtUtils.verbose info zes_smt)
     | _ -> failwith "expected a tuple")
  | _ -> failwith "expected at most"

(** Refines the first model returned by the solver by asking if
    the counter example still holds when failing only the single
    links *)
(* TODO: Avoid using this until we have support for source nodes in min-cut *)
let refineModelWithSingles (model : Nv_solution.Solution.t) info _query _chan _solve _renaming _ _ds =
  (* Find and separate the single link failures from the rest *)
  let (failed, notFailed) =
    VarMap.fold (fun fvar fval (accFailed, accNotFailed) ->
        match fval.v with
        | VBool b ->
          if b then
            begin
              (* FIXME: I have no idea if Var.name is sufficient here.
                 A better option is probably to change smt_config.multiplicities
                 to be a VarMap. *)
              let fmult = StringMap.find (Var.name fvar) SmtUtils.smt_config.SmtUtils.multiplicities in
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
      BatList.map (fun fvar -> (mk_eq (mk_var (Var.to_string fvar)) (mk_bool true))
                               |> mk_term |> mk_assert |> mk_command) failed
      |> commands_to_smt SmtUtils.smt_config.SmtUtils.verbose info
    in
    let notFailed =
      BatList.map (fun fvar -> (mk_eq (mk_var (Var.to_string fvar)) (mk_bool false))
                               |> mk_term |> mk_assert |> mk_command) notFailed
      |> commands_to_smt SmtUtils.smt_config.SmtUtils.verbose info
    in
    Some (failed ^ notFailed)
