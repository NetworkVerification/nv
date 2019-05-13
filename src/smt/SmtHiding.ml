(** * SMT encoding of network *)

open Collections
open Syntax
open Solution
open SolverUtil
open Profile
open SmtLang
open SmtExprEncodings
open SmtUtils
open SmtEncodings
open SmtOptimizations
open SmtModel
open Smt

(** Removes all variable equalities *)
(** Modified from propagate_eqs in SmtOptimizations.ml. It has the following
    differences:

    We do NOT propagate equalities between label- variables and merge-result
    variables. This allows us to selectively remove some of those equalities
    during hiding.

    We do NOT propagate equalities between constants (i.e ints/bools) and
    variables. We probably want to allow this later (TODO), but for now I
    don't want to think about it.

    We also ensure that the label- variables are used as the representatives
    for the equivalence classes of variables. *)
let propagate_eqs_for_hiding (env : smt_env) =
  let updateUnionFind eqSets s =
    try
      StringMap.find s eqSets, eqSets
    with Not_found ->
      let r = BatUref.uref s in
      r, StringMap.add s r eqSets
  in
  (* True iff this is not an equality between a label- and a merge- variable *)
  let should_propagate s1 s2 =
    not @@
    (* FIXME: The bit that checks for -result is a little fragile, since a user could
              conceivably make a variable name containing that string. If it starts
              causing problems we won't lose any precision by removing it. *)
    (BatString.starts_with s1 "label-" && BatString.starts_with s2 "merge-" && BatString.exists s2 "-result") ||
    (BatString.starts_with s2 "label-" && BatString.starts_with s1 "merge-" && BatString.exists s1 "-result")
  in
  (* Used for BatUref.unite to ensure it always selects label- variables if
     possible, so the resulting SMT program has things in terms of the attributes
     of each node *)
  let sel s1 s2 = if BatString.starts_with s1 "label-" then s1 else s2 in
  (* compute equality classes of variables and remove equalities between variables *)
  let (eqSets, valMap, new_ctx) = BatList.fold_left (fun (eqSets, valMap, acc) c ->
      match c.com with
      | Assert tm ->
        (match tm.t with
         | Eq (tm1, tm2) ->
           (match tm1, tm2 with
            | Var s1, Var s2 when should_propagate s1 s2 ->
              let r1, eqSets = updateUnionFind eqSets s1 in
              let r2, eqSets = updateUnionFind eqSets s2 in
              BatUref.unite ~sel:sel r1 r2;
              (eqSets, valMap, acc)
            (* | Var s1, Int _ | Var s1, Bool _ ->
               let valMap = StringMap.add s1 tm2 valMap in
               (eqSets, valMap, acc) *)
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

(* Right now just a copy of the solve function from Smt.ml *)
let solve_hiding info query chan ?symbolic_vars ?(params=[]) ?(starting_vars=[]) net =
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
  let renaming, full_env =
    time_profile "Encoding network"
      (fun () -> let env = Enc.encode_z3 net sym_vars in
        propagate_eqs_for_hiding env)
  in
  let env = full_env in
  (* Search out the equalities between labels and merge-results, and remove them.
     Store them in hidden_constraints until we want to put them back *)
  let hidden_constraints = 
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
